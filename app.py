from flask import Flask, request, jsonify, render_template_string
import csv
import datetime as _dt
import io
import json
import math
import os
import random
import re
import time
import urllib.parse
import urllib.request
import ssl
import html
import zipfile
import threading
import uuid
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any

# ✅ ✅ 新增：直接抓 Bingo API
def fetch_bingo_api():
    url = "https://api.taiwanlottery.com/TLCAPIWeB/WEBSERVICE/Lottery/Lottery_BingoResult.aspx"
    
    try:
        data = _request(url, timeout=10)
        text = _decode_bytes(data)
        obj = json.loads(text)
    except Exception as e:
        _log(f"API request failed: {e}")
        return []
    
    records = []
    
    # ✅ 解析資料（不同版本API用 content 或 result）
    draws = obj.get("content") or obj.get("result") or []
    
    for item in draws:
        # 嘗試找號碼欄位
        raw = str(item)
        
        # 抓 1~80 數字
        nums = re.findall(r"\b\d{1,2}\b", raw)
        numbers = [int(n) for n in nums if 1 <= int(n) <= 80]
        
        if len(numbers) >= 20:
            records.append({
                "date": item.get("DrawTime", ""),
                "period": item.get("DrawTerm", ""),
                "numbers": numbers[:20],
                "source": "api"
            })
    
    return records


app = Flask(__name__)

APP_DIR = Path(__file__).resolve().parent
CACHE_DIR = APP_DIR / "official_cache"
CACHE_DIR.mkdir(exist_ok=True)

# 政府資料開放平台：公益彩券開獎號碼及各獎項彩金相關資料
DATA_GOV_DATASET_URL = "https://data.gov.tw/dataset/72921"
DATA_GOV_INDEX_CSV = "https://gaze.nta.gov.tw/dntmb/OpenData/csvDw?ntaCode=D423F"

# 台彩官方年度資料頁：作為備援來源
TAIWAN_LOTTERY_RESULT_DOWNLOAD = "https://www.taiwanlottery.com/lotto/history/result_download/"

INDEX_CACHE = CACHE_DIR / "official_resource_index.json"
HISTORY_CACHE = CACHE_DIR / "bingobingo_history.json"
DEBUG_LOG = CACHE_DIR / "sync_debug.log"
OFFICIAL_STATE_CACHE = CACHE_DIR / "official_state.json"
PAYOUT_CACHE = CACHE_DIR / "bingobingo_payout_table.json"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/120.0 Safari/537.36"
)

GAME_KEYWORDS = ("BINGO BINGO", "Bingo Bingo", "BINGOBINGO", "賓果賓果", "賓果")

# 公司內網常見 SSL 檢查 / Proxy 會把 gaze.nta.gov.tw 的憑證換成自簽憑證，
# urllib 預設會擋下來，導致官方資料完全無法下載。
# 這裡只用在官方開放資料下載，不影響本機網頁服務。
ALLOW_UNVERIFIED_OFFICIAL_SSL = True
_SSL_CONTEXT = ssl._create_unverified_context() if ALLOW_UNVERIFIED_OFFICIAL_SSL else None


# 前端進度用：讓使用者知道目前計算到哪、還要多久。
JOBS: Dict[str, Dict[str, Any]] = {}
JOBS_LOCK = threading.Lock()

def _job_update(job_id: str, percent: int, stage: str, detail: str = "", **extra: Any) -> None:
    with JOBS_LOCK:
        job = JOBS.setdefault(job_id, {})
        job.update({
            "percent": max(0, min(100, int(percent))),
            "stage": stage,
            "detail": detail,
            "updated_at": time.time(),
        })
        job.update(extra)

def _job_get(job_id: str) -> Dict[str, Any]:
    with JOBS_LOCK:
        return dict(JOBS.get(job_id, {}))

def _estimate_seconds(record_count: int, sims: int) -> float:
    # 保守估算：資料讀取 + 權重 + 回測。不同電腦速度會不同，所以顯示為預估。
    return max(2.0, min(60.0, 1.2 + (min(max(record_count, 1), 5000) * min(max(sims, 30), 10000)) / 520000.0))


def _log(msg: str) -> None:
    ts = _dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{ts}] {msg}"
    print(line)
    try:
        with DEBUG_LOG.open("a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass


def _request(url: str, timeout: int = 30) -> bytes:
    url = _clean_url(url)
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/xml,text/csv,application/zip,*/*",
            "Accept-Language": "zh-TW,zh;q=0.9,en;q=0.7",
            "Referer": "https://www.taiwanlottery.com/",
        },
    )
    # 修正公司 Proxy / SSL Inspection 造成的 CERTIFICATE_VERIFY_FAILED。
    # 官方開放資料站偶爾會被公司憑證替換，驗證失敗時工具會連下載都做不到。
    with urllib.request.urlopen(req, timeout=timeout, context=_SSL_CONTEXT) as resp:
        return resp.read()


def _decode_bytes(data: bytes) -> str:
    for enc in ("utf-8-sig", "utf-8", "cp950", "big5", "big5hkscs", "latin1"):
        try:
            return data.decode(enc)
        except UnicodeDecodeError:
            continue
    return data.decode("utf-8", errors="replace")


def _safe_filename(name: str) -> str:
    name = re.sub(r"[\\/:*?\"<>|]+", "_", name or "download")
    return name[:180]


def _clean_url(url: str) -> str:
    """清理從 HTML/JSON 片段抓到的網址，避免 <br、換行、逗號等尾巴被當成 URL。"""
    url = html.unescape(str(url or "").strip())
    url = url.replace("\\u003C", "<").replace("\\n", "\n").replace("\\r", "\r")
    url = url.split("<", 1)[0].split(">", 1)[0]
    url = re.split(r"[\r\n\t ]+", url, maxsplit=1)[0]
    url = url.strip().strip('"\'').rstrip(");，,。]}")
    return url


def _extract_urls(text: str) -> List[str]:
    urls = []
    text = html.unescape(text or "")
    # CSV 或 HTML/JSON 中常見網址
    for m in re.finditer(r"https?://[^\s,'\"<>]+", text):
        u = _clean_url(m.group(0))
        # api-docs 是 Swagger 說明頁，不是年度資料；抓它會下載到 JSON 規格而不是獎號。
        if not u or "api-docs" in u.lower():
            continue
        if u not in urls:
            urls.append(u)
    return urls


def fetch_official_resource_index(force: bool = False) -> List[Dict[str, str]]:
    """
    下載政府資料開放平台的年度資料索引。
    索引欄位通常包含：資料所屬年度、檔案名稱、下載連結、發行屆次、發行機構。
    """
    if INDEX_CACHE.exists() and not force:
        try:
            cache = json.loads(INDEX_CACHE.read_text(encoding="utf-8"))
            if cache.get("rows"):
                return cache["rows"]
        except Exception:
            pass

    rows: List[Dict[str, str]] = []
    errors = []

    # 第一來源：政府資料開放平台 CSV 資源
    try:
        _log(f"下載官方索引：{DATA_GOV_INDEX_CSV}")
        raw = _request(DATA_GOV_INDEX_CSV, timeout=35)
        text = _decode_bytes(raw)

        # 有些環境被 gaze.nta.gov.tw 擋會回 Request Rejected HTML
        if "Request Rejected" in text or "requested URL was rejected" in text:
            raise RuntimeError("政府資料 CSV 被伺服器拒絕，改用 data.gov.tw 頁面備援解析")

        sample = text[:2048]
        dialect = csv.Sniffer().sniff(sample) if "," in sample or "\t" in sample else csv.excel
        reader = csv.DictReader(io.StringIO(text), dialect=dialect)
        for r in reader:
            cleaned = {str(k).strip(): str(v).strip() for k, v in r.items() if k is not None}
            if cleaned:
                rows.append(cleaned)

        # 如果 DictReader 因為欄位異常讀不到，就退回 URL 掃描
        if not rows:
            urls = _extract_urls(text)
            for i, u in enumerate(urls):
                rows.append({"資料所屬年度": "", "檔案名稱": f"resource_{i+1}", "下載連結": u})

    except Exception as e:
        errors.append(f"index_csv: {e}")
        _log(f"官方索引 CSV 失敗：{e}")

    # 第二來源：data.gov.tw HTML 頁面，抓資源 CSV 連結或頁面中可見連結
    if not rows:
        try:
            _log(f"下載 data.gov.tw 頁面備援：{DATA_GOV_DATASET_URL}")
            html = _decode_bytes(_request(DATA_GOV_DATASET_URL, timeout=35))
            urls = _extract_urls(html)
            for i, u in enumerate(urls):
                if "OpenData" in u or "csvDw" in u or "gaze.nta.gov.tw" in u:
                    rows.append({"資料所屬年度": "", "檔案名稱": f"data_gov_resource_{i+1}", "下載連結": u})
        except Exception as e:
            errors.append(f"data_gov_page: {e}")
            _log(f"data.gov.tw 頁面備援失敗：{e}")

    # 第三來源：台灣彩券頁面，抓 href 或圖片父層連結
    if not rows:
        try:
            _log(f"下載台彩頁面備援：{TAIWAN_LOTTERY_RESULT_DOWNLOAD}")
            html = _decode_bytes(_request(TAIWAN_LOTTERY_RESULT_DOWNLOAD, timeout=35))
            # 抓 href
            for href in re.findall(r'href=["\']([^"\']+)["\']', html, flags=re.I):
                if any(x in href.lower() for x in ("download", "opendata", ".zip", ".csv", "csvdw", "ashx")):
                    u = urllib.parse.urljoin(TAIWAN_LOTTERY_RESULT_DOWNLOAD, href)
                    rows.append({"資料所屬年度": "", "檔案名稱": Path(urllib.parse.urlparse(u).path).name or "taiwan_lottery_resource", "下載連結": u})
        except Exception as e:
            errors.append(f"taiwan_lottery_page: {e}")
            _log(f"台彩頁面備援失敗：{e}")

    if not rows:
        raise RuntimeError("官方索引下載失敗：" + " | ".join(errors))

    INDEX_CACHE.write_text(json.dumps({"updated_at": time.time(), "rows": rows}, ensure_ascii=False, indent=2), encoding="utf-8")
    return rows


def _row_get(row: Dict[str, str], *keys: str) -> str:
    # 支援欄名微差與空白
    normalized = {re.sub(r"\s+", "", k): v for k, v in row.items()}
    for key in keys:
        if key in row and row[key]:
            return row[key]
        nk = re.sub(r"\s+", "", key)
        if nk in normalized and normalized[nk]:
            return normalized[nk]
    # 模糊找
    for k, v in row.items():
        kk = re.sub(r"\s+", "", k)
        for key in keys:
            if re.sub(r"\s+", "", key) in kk and v:
                return v
    return ""


def choose_resource_rows(rows: List[Dict[str, str]], prefer_years: Optional[List[int]] = None) -> List[Dict[str, str]]:
    """
    優先抓民國當年、前一年；抓不到就全部嘗試。
    """
    if prefer_years is None:
        roc = _dt.datetime.now().year - 1911
        prefer_years = [roc, roc - 1, roc - 2]

    enriched = []
    for r in rows:
        year_text = _row_get(r, "資料所屬年度", "年度", "year")
        file_name = _row_get(r, "檔案名稱", "檔名", "name", "title")
        url = _row_get(r, "下載連結", "下載網址", "download", "url", "URL")
        if not url:
            # 有些欄位直接塞 URL
            for v in r.values():
                if isinstance(v, str) and v.startswith("http"):
                    url = v
                    break
        if not url:
            continue

        # 嘗試從年度欄或檔名抓民國年度
        y = None
        m = re.search(r"(1\d{2})", f"{year_text} {file_name} {url}")
        if m:
            try:
                y = int(m.group(1))
            except Exception:
                y = None
        enriched.append({"year": y, "file_name": file_name or f"official_{y or 'unknown'}", "url": url, "raw": r})

    preferred = [x for x in enriched if x["year"] in prefer_years]
    if preferred:
        # 年度越近越前面
        preferred.sort(key=lambda x: (x["year"] or 0), reverse=True)
        return preferred

    enriched.sort(key=lambda x: (x["year"] or 0), reverse=True)
    return enriched


def download_resource(item: Dict[str, Any], force: bool = False) -> Path:
    url = _clean_url(item["url"])

    # ✅ ✅ 關鍵修改
    if ".zip" in url.lower():
        raise Exception("Render 環境跳過 ZIP 下載（避免卡住）")
    year = item.get("year") or "unknown"
    parsed = urllib.parse.urlparse(url)
    ext = Path(parsed.path).suffix.lower()
    if not ext or len(ext) > 6:
        # gaze.nta.gov.tw 的 csvDw 下載連結常常沒有副檔名，但實際是 CSV。
        ext = ".csv" if "csvDw" in url or "csvdw" in url.lower() else ".dat"
    fname = _safe_filename(f"official_{year}_{item.get('file_name') or Path(parsed.path).name}{ext}")
    # 避免重複副檔名
    fname = re.sub(r"(\.\w+)(\.\w+)$", r"\1", fname)
    out = CACHE_DIR / fname
    if out.exists() and out.stat().st_size > 100 and not force:
        return out

    data = _request(url, timeout=60)

    # 嘗試從 Content-Disposition 取檔名不做了，保持穩定
    out.write_bytes(data)
    return out


def _resource_available(url: str, timeout: int = 12) -> bool:
    """只檢查官方年度檔是否可下載，不真的下載整包 ZIP。"""
    url = _clean_url(url)
    try:
        req = urllib.request.Request(
            url,
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "*/*",
                "Accept-Language": "zh-TW,zh;q=0.9,en;q=0.7",
                "Referer": "https://www.taiwanlottery.com/",
            },
            method="HEAD",
        )
        with urllib.request.urlopen(req, timeout=timeout, context=_SSL_CONTEXT) as resp:
            return 200 <= getattr(resp, "status", 200) < 400
    except Exception:
        # 少數 CDN 不允許 HEAD；這裡不做大檔 GET，避免首頁檢查變慢。
        return False


def _read_history_payload() -> Optional[Dict[str, Any]]:
    if not HISTORY_CACHE.exists():
        return None
    try:
        obj = json.loads(HISTORY_CACHE.read_text(encoding="utf-8"))
        if obj.get("records"):
            return obj
    except Exception:
        return None
    return None


def _parse_year_from_sources(sources: List[str]) -> Optional[int]:
    years = []
    for src in sources or []:
        m = re.search(r"official_(1\d{2})_", str(src))
        if m:
            try:
                years.append(int(m.group(1)))
            except Exception:
                pass
        # 有些路徑會帶西元年份，如 2024.zip
        m2 = re.search(r"(20\d{2})", str(src))
        if m2:
            try:
                years.append(int(m2.group(1)) - 1911)
            except Exception:
                pass
    return max(years) if years else None


def get_local_cache_summary() -> Dict[str, Any]:
    payload = _read_history_payload()
    if not payload:
        return {
            "has_cache": False,
            "record_count": 0,
            "updated_at": None,
            "cached_year": None,
            "sources": [],
            "message": "尚未建立官方資料，將自動同步。",
        }
    sources = payload.get("sources", [])
    resources = payload.get("resources", [])
    cached_year = None
    if resources:
        try:
            cached_year = max([int(x.get("year")) for x in resources if x.get("year")])
        except Exception:
            cached_year = None
    if cached_year is None:
        cached_year = _parse_year_from_sources(sources)
    return {
        "has_cache": True,
        "record_count": len(payload.get("records", [])),
        "updated_at": payload.get("updated_at"),
        "cached_year": cached_year,
        "sources": [Path(str(s)).name for s in sources],
        "resources": resources,
        "message": f"已載入官方資料 {len(payload.get('records', []))} 筆，可直接開始選號。",
    }


def check_official_update_available(force: bool = True) -> Dict[str, Any]:
    """
    輕量比對官方索引與本機快取；只提示，不自動覆蓋資料。
    force=True 代表每次開頁面都向官方索引確認一次，但不下載年度大檔。
    """
    local = get_local_cache_summary()
    try:
        rows = fetch_official_resource_index(force=force)
        candidates = choose_resource_rows(rows)
        latest = None
        checked = []
        for item in candidates[:8]:
            year = item.get("year")
            url = _clean_url(item.get("url", ""))
            if not url:
                continue
            ok = _resource_available(url)
            checked.append({"year": year, "url": url, "available": ok})
            if ok:
                latest = {"year": year, "url": url, "file_name": item.get("file_name", "")}
                break
        if not latest:
            return {**local, "ok": True, "checked_remote": True, "update_available": False, "remote_message": "目前無法確認官方最新檔案，先使用本機快取。", "checked": checked}
        cached_year = local.get("cached_year")
        update_available = (not local.get("has_cache")) or (cached_year is not None and latest.get("year") and latest["year"] > cached_year)
        if cached_year is None and local.get("has_cache"):
            update_available = False
        msg = "發現官方有較新的年度資料，可選擇更新。" if update_available else "目前快取已是可取得的最新官方年度資料。"
        return {**local, "ok": True, "checked_remote": True, "update_available": update_available, "latest_official": latest, "remote_message": msg, "checked": checked}
    except Exception as e:
        return {**local, "ok": False, "checked_remote": False, "update_available": False, "remote_message": f"官方更新檢查失敗，先使用本機快取：{e}"}


def _numbers_from_values(values: List[str], allow_embedded: bool = False) -> List[int]:
    """
    從欄位值抓號碼。
    預設只接受整格就是 01~80 的值，避免把日期、期別、金額誤抓成號碼。
    allow_embedded=True 僅用於「獎號欄」或官方把 20 顆獎號塞在同一格時。
    """
    nums = []
    for v in values:
        if v is None:
            continue
        s = str(v).strip()
        candidates = []
        if re.fullmatch(r"0?\d{1,2}", s):
            candidates = [s]
        elif allow_embedded:
            # 只在獎號相關欄位使用，支援「01 02 03...」或「01,02,03...」
            candidates = re.findall(r"(?<!\d)0?\d{1,2}(?!\d)", s)
        for c in candidates:
            try:
                n = int(c)
            except Exception:
                continue
            if 1 <= n <= 80:
                nums.append(n)
    # 去重但保留順序
    out = []
    for n in nums:
        if n not in out:
            out.append(n)
    return out


def _is_award_number_key(key: str) -> bool:
    """判斷欄名是否為官方獎號欄。"""
    k = str(key or "").strip().replace(" ", "")
    return (
        "獎號" in k
        or "開出順序" in k
        or re.fullmatch(r"(n|no|num|number)\d+", k, flags=re.I) is not None
        or re.fullmatch(r"號碼\d+", k) is not None
    )


def _extract_bingo_numbers_from_dict_row(row: Dict[str, str]) -> List[int]:
    """
    官方年度 ZIP 內每個遊戲通常是獨立 CSV，BINGO BINGO 檔案的每列會有獎號1~獎號20。
    注意：ZIP 內中文檔名常會變亂碼，因此不能靠檔名或列內遊戲名稱判斷；
    只要同一列能從「獎號欄」解析出 20 顆 1~80 且不重複，就視為 BINGO BINGO 紀錄。
    """
    # 1) 優先讀 獎號1~獎號20 / 號碼1~號碼20 / N1~N20
    ordered_values = []
    for i in range(1, 21):
        found = ""
        candidates = (
            f"獎號{i}", f"獎號 {i}", f"號碼{i}", f"號碼 {i}",
            f"No{i}", f"NO{i}", f"N{i}", f"n{i}", f"number{i}", f"Number{i}",
        )
        for key in candidates:
            if key in row and row[key] != "":
                found = row[key]
                break
        if found != "":
            ordered_values.append(found)
    nums = _numbers_from_values(ordered_values, allow_embedded=True)
    if len(nums) >= 20:
        return nums[:20]

    # 2) 欄名可能是「第1獎號」「獎號01」「獎號一」或帶說明文字，改用模糊抓所有獎號欄
    award_values = [v for k, v in row.items() if _is_award_number_key(k)]
    nums = _numbers_from_values(award_values, allow_embedded=True)
    if len(nums) >= 20:
        return nums[:20]

    # 3) 少數官方檔可能把 20 顆獎號塞在單一欄位，例如「開獎號碼」
    packed_values = []
    for k, v in row.items():
        kk = str(k or "")
        if any(x in kk for x in ("開獎號碼", "中獎號碼", "獎號", "號碼")):
            packed_values.append(v)
    nums = _numbers_from_values(packed_values, allow_embedded=True)
    if len(nums) >= 20:
        return nums[:20]

    return []


def _is_bingo_row(row: Dict[str, str]) -> bool:
    joined = " ".join(str(v) for v in row.values())
    return any(k.lower() in joined.lower() for k in GAME_KEYWORDS)


def _parse_csv_text(text: str, source: str = "") -> List[Dict[str, Any]]:
    records = []

    # 有些官方 CSV 前幾行有 BOM 或說明，嘗試直接 DictReader；失敗再用一般 reader
    try:
        sample = text[:4096]
        dialect = csv.Sniffer().sniff(sample) if ("," in sample or "\t" in sample) else csv.excel
    except Exception:
        dialect = csv.excel

    f = io.StringIO(text)
    reader = csv.DictReader(f, dialect=dialect)
    fieldnames = reader.fieldnames or []

    # 官方年度 ZIP 內通常是一個遊戲一個 CSV。
    # BINGO BINGO 的列不一定含「BINGO BINGO」文字，因此不可強制 _is_bingo_row(row)。
    # 判斷重點改為：從獎號欄可解析出 20 顆 1~80 不重複號碼。
    if fieldnames and any(_is_award_number_key(str(x)) for x in fieldnames):
        for row in reader:
            row = {str(k).strip(): ("" if v is None else str(v).strip()) for k, v in row.items() if k is not None}
            nums = _extract_bingo_numbers_from_dict_row(row)
            if len(nums) >= 20:
                records.append({
                    "date": _row_get(row, "開獎日期", "日期", "draw_date", "開獎日"),
                    "period": _row_get(row, "期別", "期號", "draw_no", "期數"),
                    "numbers": nums[:20],
                    "source": source,
                })
        if records:
            return records

    # fallback 1：有些 CSV 欄名亂碼但列內仍含 BINGO / 賓果文字
    f.seek(0)
    plain_reader = csv.reader(f, dialect=dialect)
    for row in plain_reader:
        joined = " ".join(str(x) for x in row)
        if not any(k.lower() in joined.lower() for k in GAME_KEYWORDS):
            continue
        nums = _numbers_from_values(row, allow_embedded=True)
        if len(nums) >= 20:
            records.append({"date": "", "period": "", "numbers": nums[:20], "source": source})

    if records:
        return records

    # fallback 2：針對官方一遊戲一檔，但檔名/欄名都因 ZIP 編碼亂掉的狀況。
    # 僅接受「同一列剛好能抓到至少20顆、且不重複、1~80」的資料，降低誤判大樂透/威力彩機率。
    f.seek(0)
    plain_reader = csv.reader(f, dialect=dialect)
    for row in plain_reader:
        nums = _numbers_from_values(row, allow_embedded=True)
        if len(nums) >= 20:
            records.append({"date": "", "period": "", "numbers": nums[:20], "source": source})

    return records


def _parse_json_text(text: str, source: str = "") -> List[Dict[str, Any]]:
    records = []
    obj = json.loads(text)
    if isinstance(obj, dict):
        # 找第一個 list
        candidates = []
        for v in obj.values():
            if isinstance(v, list):
                candidates = v
                break
        if not candidates:
            candidates = [obj]
    elif isinstance(obj, list):
        candidates = obj
    else:
        candidates = []

    for item in candidates:
        if isinstance(item, dict):
            row = {str(k): "" if v is None else str(v) for k, v in item.items()}
            if not _is_bingo_row(row):
                continue
            vals = []
            for i in range(1, 21):
                for key in (f"獎號{i}", f"n{i}", f"N{i}", f"號碼{i}"):
                    if key in row:
                        vals.append(row[key])
                        break
            nums = _numbers_from_values(vals)
            if len(nums) < 20:
                nums = _numbers_from_values(list(row.values()))
            if len(nums) >= 20:
                records.append({
                    "date": _row_get(row, "開獎日期", "日期"),
                    "period": _row_get(row, "期別", "期號"),
                    "numbers": nums[:20],
                    "source": source,
                })
    return records


def parse_official_file(path: Path) -> List[Dict[str, Any]]:
    records: List[Dict[str, Any]] = []
    suffix = path.suffix.lower()

    try:
        if zipfile.is_zipfile(path):
            with zipfile.ZipFile(path) as z:
                for name in z.namelist():
                    low = name.lower()
                    if not low.endswith((".csv", ".txt", ".json")):
                        continue
                    _log(f"解析 ZIP 內檔案：{name}")
                    data = z.read(name)
                    text = _decode_bytes(data)
                    if low.endswith(".json"):
                        records.extend(_parse_json_text(text, source=f"{path.name}/{name}"))
                    else:
                        records.extend(_parse_csv_text(text, source=f"{path.name}/{name}"))

        elif suffix in (".csv", ".txt", ".dat"):
            text = _decode_bytes(path.read_bytes())
            records.extend(_parse_csv_text(text, source=path.name))

        elif suffix == ".json":
            text = _decode_bytes(path.read_bytes())
            records.extend(_parse_json_text(text, source=path.name))

        elif suffix in (".xlsx", ".xlsm"):
            # 非必要依賴，有安裝 openpyxl 才支援
            try:
                import openpyxl
                wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
                for ws in wb.worksheets:
                    rows = list(ws.iter_rows(values_only=True))
                    if not rows:
                        continue
                    headers = [str(x).strip() if x is not None else "" for x in rows[0]]
                    for raw in rows[1:]:
                        row = {headers[i]: "" if raw[i] is None else str(raw[i]).strip() for i in range(min(len(headers), len(raw)))}
                        if not _is_bingo_row(row):
                            continue
                        nums = []
                        for i in range(1, 21):
                            nums.append(row.get(f"獎號{i}", ""))
                        nums = _numbers_from_values(nums)
                        if len(nums) >= 20:
                            records.append({"date": _row_get(row, "開獎日期", "日期"), "period": _row_get(row, "期別"), "numbers": nums[:20], "source": path.name})
            except Exception as e:
                _log(f"Excel 解析略過：{e}")

    except Exception as e:
        _log(f"解析檔案失敗 {path}: {e}")

    # 去重：期別+日期+號碼
    seen = set()
    out = []
    for r in records:
        key = (r.get("period", ""), r.get("date", ""), tuple(r.get("numbers", [])))
        if key not in seen:
            seen.add(key)
            out.append(r)
    return out

# ✅ ✅ Step 1：優先用官方 API（快速可靠）
    try:
        records = fetch_bingo_api()
        if len(records) >= 100:
            return {
                "ok": True,
                "from_cache": False,
                "records": records[:1000],  # 限制筆數避免過大
                "record_count": len(records),
                "message": f"✅ 使用官方API資料，共 {len(records)} 筆"
            }
    except Exception as e:
        _log(f"API fallback error: {e}")

def sync_official_data(force: bool = False):
    """
    ✅ 改成直接用 API（完全不跑 CSV / ZIP）
    """
    data = get_data()

    return {
        "ok": True,
        "from_cache": False,
        "records": [{"numbers": d} for d in data],
        "record_count": len(data),
        "message": f"✅ API資料已載入，共 {len(data)} 筆"
    }


def get_data(force_sync: bool = False):
    """
    ✅ 直接抓 Bingo 開獎 API
    """
    url = "https://api.taiwanlottery.com/TLCAPIWeB/WEBSERVICE/Lottery/Lottery_BingoResult.aspx"

    try:
        data = _request(url, timeout=10)
        text = _decode_bytes(data)
        obj = json.loads(text)
    except Exception as e:
        _log(f"API失敗: {e}")
        return []

    results = []

    draws = obj.get("content") or obj.get("result") or []

    for item in draws:
        raw = str(item)

        nums = re.findall(r"\b\d{1,2}\b", raw)
        numbers = [int(n) for n in nums if 1 <= int(n) <= 80]

        if len(numbers) >= 20:
            results.append(numbers[:20])

    return results[:500]  # ✅ 限制500筆，加快速度


def filter_weekday(data: List[List[int]]) -> List[List[int]]:
    # 原工具保留：若真的要 weekday_filter 才會用
    weekday = _dt.datetime.now().weekday()
    return [d for i, d in enumerate(data) if i % 7 == weekday]



def build_scores(data: List[List[int]], strategy: str = "平衡型", lookback: int = 300) -> Dict[int, float]:
    """
    依官方歷史資料建立 01~80 的分數。
    注意：這不是必中公式，而是把長期頻率、近期頻率、遺漏值與穩定性整合成可回測的分數。
    """
    # 純隨機作為基準線：所有號碼權重相同。
    if strategy == "純隨機":
        return {i: 1.0 for i in range(1, 81)}

    if not data:
        return {i: 1.0 for i in range(1, 81)}

    recent = data[-lookback:] if lookback and len(data) > lookback else data
    long_counter = Counter()
    recent_counter = Counter()
    first_half = Counter()
    second_half = Counter()

    for row in data:
        long_counter.update(row)
    for row in recent:
        recent_counter.update(row)

    # 近期趨勢：把 lookback 切成前半/後半，避免只看總熱度。
    mid = max(1, len(recent) // 2)
    for row in recent[:mid]:
        first_half.update(row)
    for row in recent[mid:]:
        second_half.update(row)

    # 遺漏值：從最新往前找最後一次出現。
    miss = {n: len(recent) + 1 for n in range(1, 81)}
    for idx, row in enumerate(reversed(recent), start=1):
        for n in row:
            if miss[n] == len(recent) + 1:
                miss[n] = idx

    def norm(v, maxv):
        return 0.0 if maxv <= 0 else v / maxv

    max_long = max(long_counter.values() or [1])
    max_recent = max(recent_counter.values() or [1])
    max_miss = max(miss.values() or [1])
    max_trend_abs = max([abs(second_half[n] - first_half[n]) for n in range(1, 81)] or [1])

    scores = {}
    for n in range(1, 81):
        freq_score = norm(long_counter[n], max_long)
        recent_score = norm(recent_counter[n], max_recent)
        miss_score = norm(miss[n], max_miss)
        trend_raw = second_half[n] - first_half[n]
        trend_score = 0.5 + (trend_raw / max_trend_abs / 2 if max_trend_abs else 0)
        trend_score = max(0.0, min(1.0, trend_score))

        if strategy == "保守型":
            # 偏熱號與穩定近期表現，降低太久沒開的號碼。
            score = freq_score * 0.38 + recent_score * 0.42 + trend_score * 0.12 + (1 - miss_score) * 0.08
        elif strategy == "逆向型":
            # 偏冷號與遺漏值，但保留一點近期趨勢，避免完全賭冷。
            score = (1 - freq_score) * 0.26 + (1 - recent_score) * 0.22 + miss_score * 0.38 + trend_score * 0.09 + random.random() * 0.05
        else:
            # 平衡型：熱度、趨勢、遺漏值都看，少量隨機避免每次完全固定。
            score = freq_score * 0.26 + recent_score * 0.31 + miss_score * 0.22 + trend_score * 0.14 + random.random() * 0.07

        scores[n] = max(score, 0.0001)

    return scores


def _bucket_of_number(n: int) -> int:
    # 01~20 / 21~40 / 41~60 / 61~80
    return min(3, max(0, (int(n) - 1) // 20))


def _pick_balanced_from_candidates(candidates: List[int], scores: Dict[int, float], count: int) -> List[int]:
    """從候選池中貪婪挑選，加入區間、奇偶、尾數與距離分散，避免組合太偏。"""
    picked: List[int] = []
    count = min(count, len(candidates))
    target_bucket = max(1, math.ceil(count / 4))

    while len(picked) < count:
        best_n = None
        best_score = -10**9
        for n in candidates:
            if n in picked:
                continue
            base = float(scores.get(n, 0.0001))
            bucket_used = sum(1 for x in picked if _bucket_of_number(x) == _bucket_of_number(n))
            parity_used = sum(1 for x in picked if x % 2 == n % 2)
            tail_used = sum(1 for x in picked if x % 10 == n % 10)
            close_used = sum(1 for x in picked if abs(x - n) <= 2)

            penalty = 0.0
            if bucket_used >= target_bucket:
                penalty += base * 0.28
            if parity_used > len(picked) / 2 + 1:
                penalty += base * 0.16
            if tail_used >= 1:
                penalty += base * 0.12
            if close_used >= 1:
                penalty += base * 0.10

            # 小幅隨機只用來打破同分，不讓結果每次完全死板。
            final = base - penalty + random.random() * 0.002
            if final > best_score:
                best_score = final
                best_n = n
        if best_n is None:
            break
        picked.append(best_n)

    return sorted(picked)


def pick_numbers(scores: Dict[int, float], count: int, number_range: str = "1-80") -> List[int]:
    if number_range == "1-40":
        allowed = list(range(1, 41))
    elif number_range == "41-80":
        allowed = list(range(41, 81))
    else:
        allowed = list(range(1, 81))

    nums = [n for n in allowed if n in scores]
    if not nums:
        return []

    count = min(max(1, int(count)), len(nums))
    values = [float(scores[n]) for n in nums]

    # 純隨機基準：所有權重相同時，不做候選池平衡，保持真正隨機。
    if max(values) - min(values) < 1e-12:
        return sorted(random.sample(nums, count))

    # 候選池 + 平衡挑選：先取高分候選，再做區間/奇偶/尾數分散。
    ranked = sorted(nums, key=lambda n: scores.get(n, 0), reverse=True)
    pool_size = min(len(ranked), max(20, count * 5))
    candidates = ranked[:pool_size]
    return _pick_balanced_from_candidates(candidates, scores, count)

# BINGO BINGO 基本玩法獎金表：以每注 25 元計算。
# key = 選號數量, value = {命中顆數: 獎金}
# 工具會優先使用官方同步/快取的獎金表；若官方頁面無法解析，才使用這份未同步｜官方基準表。
DEFAULT_PAYOUT_TABLE = {
    # 官方基本玩法，不含超級獎號，以每注 25 元計算。
    1: {1: 50},
    2: {1: 25, 2: 75},
    3: {2: 50, 3: 500},
    4: {2: 25, 3: 100, 4: 1000},
    5: {3: 50, 4: 500, 5: 7500},
    6: {3: 25, 4: 200, 5: 1000, 6: 25000},
    7: {3: 25, 4: 50, 5: 300, 6: 3000, 7: 80000},
    8: {0: 25, 4: 25, 5: 200, 6: 1000, 7: 20000, 8: 500000},
    9: {0: 25, 4: 25, 5: 100, 6: 500, 7: 3000, 8: 100000, 9: 1000000},
    10: {0: 25, 5: 25, 6: 250, 7: 2500, 8: 25000, 9: 250000, 10: 5000000},
}

# 保留舊名稱，避免其他地方仍有相容性需求。
PAYOUT_TABLE = DEFAULT_PAYOUT_TABLE
PAYOUT_OFFICIAL_SOURCES = [
    # 只保留目前有效的官方來源，避免 log 一直出現已知無效網址。
    # 1) 官方頁面直連：成功時最快；若 HTML 結構不利解析，會安靜略過。
    "https://www.taiwanlottery.com/lotto/info/bingo_bingo/",
    # 2) 官方頁面文字版：目前最穩定的獎金表同步路徑。
    #    來源仍是台彩官方頁，只是轉成較好解析的文字。
    "https://r.jina.ai/http://r.jina.ai/http://https://www.taiwanlottery.com/lotto/info/bingo_bingo/",
]
_PAYOUT_MEMORY: Optional[Dict[str, Any]] = None


def _payout_display_url(url: str) -> str:
    """把備援讀取網址轉成乾淨可讀的官方來源文字，避免 log 顯示一長串 r.jina.ai。"""
    marker = "https://r.jina.ai/http://r.jina.ai/http://"
    if url.startswith(marker):
        return "文字化官方頁：" + url[len(marker):]
    return url


def _payout_cache_is_official() -> bool:
    """判斷本機是否已有成功解析的官方獎金表快取。"""
    if not PAYOUT_CACHE.exists():
        return False
    try:
        payload = json.loads(PAYOUT_CACHE.read_text(encoding="utf-8"))
        table = _normalize_payout_table(payload.get("table"))
        return bool(table and payload.get("ok") and payload.get("source") == "官方獎金表")
    except Exception:
        return False

def _recent_official_payout_payload(max_age_seconds: int = 300) -> Optional[Dict[str, Any]]:
    """回傳短時間內剛同步成功的官方獎金表；避免首頁載入後手動同步又重抓一次。"""
    if not PAYOUT_CACHE.exists():
        return None
    try:
        if time.time() - PAYOUT_CACHE.stat().st_mtime > max_age_seconds:
            return None
        payload = json.loads(PAYOUT_CACHE.read_text(encoding="utf-8"))
        table = _normalize_payout_table(payload.get("table"))
        if table and payload.get("ok") and payload.get("source") == "官方獎金表":
            payload["table"] = table
            return payload
    except Exception:
        return None
    return None


def _clone_payout_table(table: Dict[int, Dict[int, int]]) -> Dict[int, Dict[int, int]]:
    return {int(k): {int(h): int(v) for h, v in vals.items()} for k, vals in table.items()}


def _normalize_payout_table(obj: Any) -> Optional[Dict[int, Dict[int, int]]]:
    if not isinstance(obj, dict):
        return None
    table: Dict[int, Dict[int, int]] = {}
    for star_key, hit_map in obj.items():
        try:
            star = int(str(star_key).replace("星", "").strip())
        except Exception:
            continue
        if not (1 <= star <= 10) or not isinstance(hit_map, dict):
            continue
        table[star] = {}
        for hit_key, prize in hit_map.items():
            try:
                hit = int(str(hit_key).replace("中", "").replace("顆", "").strip())
                amount = int(str(prize).replace(",", "").replace("元", "").strip())
            except Exception:
                continue
            if 0 <= hit <= star and amount >= 0:
                table[star][hit] = amount
    # 至少要能覆蓋常用 1~10 星，才視為有效官方獎金表。
    valid_count = sum(1 for i in range(1, 11) if table.get(i))
    if valid_count >= 8:
        for i in range(1, 11):
            table.setdefault(i, _clone_payout_table(DEFAULT_PAYOUT_TABLE).get(i, {}))
        return table
    return None



def _table_matches_official_anchor(table: Dict[int, Dict[int, int]]) -> bool:
    """用幾個官方關鍵值防止抓到錯表或超級獎號表。"""
    anchors = {
        1: {1: 50},
        2: {1: 25, 2: 75},
        8: {8: 500000, 0: 25},
        9: {9: 1000000, 8: 100000, 0: 25},
        10: {10: 5000000, 9: 250000, 8: 25000, 0: 25},
    }
    try:
        for star, pairs in anchors.items():
            for hit, amount in pairs.items():
                if int(table.get(star, {}).get(hit, -1)) != amount:
                    return False
        return True
    except Exception:
        return False


def _official_aligned_payload(message: str = "官方頁面暫時無法解析，使用已依官方基本玩法校正的基準表") -> Dict[str, Any]:
    return _payout_payload(
        DEFAULT_PAYOUT_TABLE,
        "未同步｜官方基準表",
        source_url="",
        ok=True,
        message=message,
    )

def _payout_payload(table: Dict[int, Dict[int, int]], source: str, source_url: str = "", ok: bool = True, message: str = "") -> Dict[str, Any]:
    return {
        "ok": ok,
        "table": _clone_payout_table(table),
        "bet_amount": 25,
        "source": source,
        "source_url": source_url,
        "updated_at": _dt.datetime.now().isoformat(timespec="seconds"),
        "message": message or source,
    }


def _extract_payout_table_from_text(text: str) -> Optional[Dict[int, Dict[int, int]]]:
    """嘗試從官方 HTML/PDF 文字抽出 1~10 星基本玩法獎金表。解析不到就回 None，不覆蓋舊快取。"""
    if not text:
        return None
    clean = html.unescape(text)
    clean = re.sub(r"[　 ]+", " ", clean)
    clean = re.sub(r"<[^>]+>", " ", clean)
    clean = re.sub(r"\s+", " ", clean)

    # 若官方頁面未來直接提供類似 JSON 的獎金表，優先吃這種乾淨格式。
    json_patterns = [
        r"PAYOUT_TABLE\s*=\s*(\{.*?\})\s*;",
        r"payoutTable\s*[:=]\s*(\{.*?\})\s*[,;]",
        r"prizeTable\s*[:=]\s*(\{.*?\})\s*[,;]",
    ]
    for pat in json_patterns:
        m = re.search(pat, clean, flags=re.I | re.S)
        if not m:
            continue
        try:
            obj = json.loads(m.group(1))
            table = _normalize_payout_table(obj)
            if table:
                return table
        except Exception:
            pass

    # 台彩官方頁面若能抓到完整獎金分配文字，先用關鍵值確認是 BINGO BINGO 官方基本玩法表，
    # 再回傳已校正過的官方基本玩法表。這樣避免 HTML 表格中的「固定倍數 / 單注獎金 / 上限」被誤抓。
    required_phrases = ["BINGO BINGO", "基本玩法", "所有獎項皆為固定獎金"]
    required_numbers = ["10星", "中10", "5,000,000", "9星", "1,000,000", "1星", "50"]
    if all(p in clean for p in required_phrases) and all(p in clean for p in required_numbers):
        return _clone_payout_table(DEFAULT_PAYOUT_TABLE)

    # 文字式備援解析：偏保守，只接受解析後能通過官方關鍵值驗證的表。
    table: Dict[int, Dict[int, int]] = {}
    for star in range(1, 11):
        star_pat = rf"{star}\s*星(.{{0,1800}}?)(?:{star + 1}\s*星|超級獎號|猜大小|猜單雙|$)"
        sm = re.search(star_pat, clean)
        if not sm:
            continue
        segment = sm.group(1)
        hits: Dict[int, int] = {}
        for hit in range(0, star + 1):
            # 優先抓含 $ / NT$ / 新台幣 的單注獎金，避開前面的固定獎金倍數。
            hm = re.search(rf"中\s*{hit}[^$NT新台幣]{{0,80}}(?:NT\$|\$|新台幣)\s*([0-9][0-9,]{{0,12}})", segment, flags=re.I)
            if not hm:
                continue
            try:
                prize = int(hm.group(1).replace(",", ""))
            except Exception:
                continue
            if prize > 0:
                hits[hit] = prize
        if hits:
            table[star] = hits
    table2 = _normalize_payout_table(table)
    if table2 and _table_matches_official_anchor(table2):
        return table2
    return None


def sync_payout_table(force: bool = False) -> Dict[str, Any]:
    """更新官方獎金表快取；主控台只顯示最後結果，備援嘗試細節不再洗版。"""
    global _PAYOUT_MEMORY
    if _PAYOUT_MEMORY and not force:
        return _PAYOUT_MEMORY

    if PAYOUT_CACHE.exists() and not force:
        try:
            payload = json.loads(PAYOUT_CACHE.read_text(encoding="utf-8"))
            table = _normalize_payout_table(payload.get("table"))
            if table:
                payload["table"] = table
                _PAYOUT_MEMORY = payload
                return payload
        except Exception:
            pass

    # 非強制狀態不主動重抓，避免首頁一直跑同步；沒有快取才暫用基準表。
    if not force:
        payload = _official_aligned_payload("尚未取得官方同步結果，先使用已依官方基本玩法校正的基準表")
        _PAYOUT_MEMORY = payload
        return payload

    _log("官方獎金表同步中...")
    errors = []
    attempts = []
    for url in PAYOUT_OFFICIAL_SOURCES:
        display_url = _payout_display_url(url)
        attempts.append(display_url)
        try:
            raw = _request(url, timeout=15)
            text = _decode_bytes(raw)
            if url.lower().endswith(".pdf"):
                try:
                    from pypdf import PdfReader  # type: ignore
                    reader = PdfReader(io.BytesIO(raw))
                    text = "\n".join(page.extract_text() or "" for page in reader.pages)
                except Exception as e:
                    errors.append(f"{display_url}: PDF解析失敗 {e}")
                    continue
            table = _extract_payout_table_from_text(text)
            if table:
                payload = _payout_payload(table, "官方獎金表", source_url=display_url, ok=True, message="官方獎金表已更新")
                PAYOUT_CACHE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
                _PAYOUT_MEMORY = payload
                _log(f"官方獎金表同步成功：{display_url}")
                return payload
            errors.append(f"{display_url}: 下載成功但未解析到有效表格")
        except Exception as e:
            errors.append(f"{display_url}: {e}")

    # 解析失敗時不覆蓋舊快取；只有「官方獎金表」快取才標示為官方來源。
    if PAYOUT_CACHE.exists():
        try:
            payload = json.loads(PAYOUT_CACHE.read_text(encoding="utf-8"))
            table = _normalize_payout_table(payload.get("table"))
            if table and payload.get("source") == "官方獎金表":
                payload["table"] = table
                payload["ok"] = True
                payload["message"] = "官方獎金表同步失敗，沿用上次官方快取"
                _PAYOUT_MEMORY = payload
                _log("官方獎金表同步失敗，已沿用上次官方快取")
                return payload
        except Exception:
            pass

    detail = "；".join(str(x) for x in errors[-3:]) if errors else "無可用來源"
    _log(f"官方獎金表同步失敗，已使用官方基準表｜{detail}")
    payload = _official_aligned_payload("官方獎金表暫時無法解析，已使用已依官方基本玩法校正的基準表")
    _PAYOUT_MEMORY = payload
    return payload


def get_payout_table(force: bool = False) -> Dict[int, Dict[int, int]]:
    return _clone_payout_table(sync_payout_table(force=force).get("table", DEFAULT_PAYOUT_TABLE))


def get_payout_summary(force: bool = False) -> Dict[str, Any]:
    payload = sync_payout_table(force=force)
    return {
        "ok": bool(payload.get("ok")),
        "source": payload.get("source", "未同步｜官方基準表"),
        "updated_at": payload.get("updated_at"),
        "bet_amount": payload.get("bet_amount", 25),
        "message": payload.get("message", ""),
    }


def theoretical_random_baseline(count: int, payout_table: Optional[Dict[int, Dict[int, int]]] = None) -> Dict[str, Any]:
    """BINGO BINGO 80 選 20，玩家固定選 count 顆時的理論隨機基準。"""
    count = max(1, min(10, int(count)))
    total = math.comb(80, count)
    dist: Dict[str, float] = {}
    for h in range(0, count + 1):
        if h <= 20 and count - h <= 60:
            prob = math.comb(20, h) * math.comb(60, count - h) / total
        else:
            prob = 0.0
        dist[str(h)] = round(prob * 100, 4)

    avg_hits = count * 20 / 80
    hit_rate = 100 - dist.get("0", 0.0)
    ge2 = sum(v for k, v in dist.items() if int(k) >= 2)
    ge3 = sum(v for k, v in dist.items() if int(k) >= 3)
    table = payout_table or get_payout_table(force=False)
    expected_return = 0.0
    for h, prize in table.get(count, {}).items():
        expected_return += (dist.get(str(h), 0.0) / 100) * prize
    return_rate = expected_return / 25 * 100
    return {
        "hit_rate": round(hit_rate, 2),
        "avg_hits": round(avg_hits, 2),
        "ge2_rate": round(ge2, 2),
        "ge3_rate": round(ge3, 2),
        "return_rate": round(return_rate, 2),
        "hit_distribution": dist,
    }


def backtest(data: List[List[int]], count: int, strategy: str, sims: int = 300, lookback: int = 300, number_range: str = "1-80", progress_cb=None, payout_table: Optional[Dict[int, Dict[int, int]]] = None) -> Dict[str, Any]:
    table = payout_table or get_payout_table(force=False)
    if len(data) < 50:
        base = theoretical_random_baseline(count, payout_table=table)
        return {
            "hit_rate": 0, "avg_hits": 0, "return_rate": 0, "max_losing_streak": 0, "rounds": 0,
            "ge2_rate": 0, "ge3_rate": 0, "hit_distribution": {}, "random_baseline": base,
            "vs_random_hit_rate": 0, "vs_random_return_rate": 0,
        }

    rounds = min(max(30, sims), max(30, len(data) - 30))
    start = max(20, len(data) - rounds)
    hits_list: List[int] = []
    total_return = 0
    bet = 25
    losing = 0
    max_losing = 0

    total_rounds = max(1, len(data) - start)
    for idx, i in enumerate(range(start, len(data)), start=1):
        if progress_cb and (idx == 1 or idx == total_rounds or idx % max(1, total_rounds // 20) == 0):
            progress_cb(idx, total_rounds)
        train = data[:i]
        actual = set(data[i])
        if strategy == "純隨機":
            scores = {n: 1.0 for n in range(1, 81)}
        else:
            scores = build_scores(train, strategy=strategy, lookback=lookback)
        picked = set(pick_numbers(scores, count, number_range=number_range))
        hit = len(picked & actual)
        hits_list.append(hit)
        prize = table.get(count, {}).get(hit, 0)
        total_return += prize
        if prize <= 0:
            losing += 1
            max_losing = max(max_losing, losing)
        else:
            losing = 0

    any_hit_rate = sum(1 for h in hits_list if h > 0) / len(hits_list) * 100 if hits_list else 0
    ge2_rate = sum(1 for h in hits_list if h >= 2) / len(hits_list) * 100 if hits_list else 0
    ge3_rate = sum(1 for h in hits_list if h >= 3) / len(hits_list) * 100 if hits_list else 0
    avg_hits = sum(hits_list) / len(hits_list) if hits_list else 0
    return_rate = total_return / (len(hits_list) * bet) * 100 if hits_list else 0
    dist_counter = Counter(hits_list)
    hit_distribution = {str(i): round(dist_counter.get(i, 0) / len(hits_list) * 100, 2) for i in range(0, count + 1)} if hits_list else {}
    baseline = theoretical_random_baseline(count, payout_table=table)

    return {
        "hit_rate": round(any_hit_rate, 2),
        "ge2_rate": round(ge2_rate, 2),
        "ge3_rate": round(ge3_rate, 2),
        "avg_hits": round(avg_hits, 2),
        "return_rate": round(return_rate, 2),
        "max_losing_streak": max_losing,
        "rounds": len(hits_list),
        "hit_distribution": hit_distribution,
        "random_baseline": baseline,
        "vs_random_hit_rate": round(any_hit_rate - baseline.get("hit_rate", 0), 2),
        "vs_random_return_rate": round(return_rate - baseline.get("return_rate", 0), 2),
    }


def optimize_lookback(data: List[List[int]], count: int, strategy: str, number_range: str = "1-80", progress_cb=None) -> Dict[str, Any]:
    """
    用較短的快速回測找比較適合的統計週期。
    目的不是曲線擬合，而是避免固定 300 期在不同資料量下失真。
    """
    candidates = [50, 100, 300, 500, 1000]
    candidates = [x for x in candidates if len(data) >= max(60, x // 2)] or [300]
    quick_sims = min(120, max(30, len(data) - 30))
    results = []
    total = len(candidates)
    for idx, lb in enumerate(candidates, start=1):
        if progress_cb:
            progress_cb(idx, total, lb)
        bt = backtest(data, count=count, strategy=strategy, sims=quick_sims, lookback=lb, number_range=number_range)
        # 排序分數：回收率優先，其次中3+比例、平均命中，再看是否高於隨機。
        score = bt.get("return_rate", 0) * 0.50 + bt.get("ge3_rate", 0) * 0.22 + bt.get("avg_hits", 0) * 10 * 0.18 + bt.get("vs_random_hit_rate", 0) * 0.10
        results.append({"lookback": lb, "score": round(score, 4), "backtest": bt})
    results.sort(key=lambda x: x["score"], reverse=True)
    best = results[0] if results else {"lookback": 300, "score": 0, "backtest": {}}
    return {"best_lookback": best["lookback"], "results": results, "quick_sims": quick_sims}

HTML = r"""
<!doctype html>
<html lang="zh-Hant">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>BINGO BINGO 智慧選號工具</title>
<style>
:root{
  --wine-1:#5a0000;
  --wine-2:#280000;
  --wine-3:#780606;
  --cream:#fffaf4;
  --cream-2:#fffdf9;
  --cream-3:#fff4e6;
  --line:#ead9c9;
  --line-2:#f2dfca;
  --text:#3e2220;
  --muted:#7d6962;
  --red:#bd1220;
  --red-2:#7c0008;
  --gold:#f6b33f;
  --gold-2:#ffe092;
  --shadow:0 20px 48px rgba(0,0,0,.22);
}
*{box-sizing:border-box}
html,body{min-height:100%;margin:0}
body{
  font-family:"Microsoft JhengHei UI","Noto Sans TC",Arial,sans-serif;
  background:
    radial-gradient(circle at 10% 8%,rgba(255,191,77,.12),transparent 28%),
    radial-gradient(circle at 88% 18%,rgba(255,71,71,.10),transparent 24%),
    linear-gradient(180deg,var(--wine-1),var(--wine-2) 52%,var(--wine-3));
  color:#fff2dd;
}
.wrap{max-width:1360px;margin:0 auto;padding:26px 24px 42px;}
.topbar{display:flex;align-items:center;justify-content:flex-start;gap:18px;margin-bottom:18px}
.brand{display:flex;align-items:center;gap:16px}
.logo{
  width:68px;height:68px;border-radius:18px;display:grid;place-items:center;
  background:linear-gradient(180deg,rgba(20,0,0,.72),rgba(70,0,0,.52));
  box-shadow:inset 0 1px 0 rgba(255,255,255,.08),0 12px 26px rgba(0,0,0,.22)
}
.logoGrid{display:grid;grid-template-columns:repeat(3,13px);gap:6px}
.logoGrid span{width:13px;height:13px;border-radius:50%;background:linear-gradient(180deg,#fff1ad,#f2b33b);box-shadow:0 2px 6px rgba(0,0,0,.18)}
.brand h1{margin:0;font-size:30px;letter-spacing:.4px;font-weight:950;line-height:1.1}
.brand .subtitle{margin-top:7px;color:#f7dbc2;font-size:14px;font-weight:800}
.card{
  background:rgba(255,250,244,.985);
  color:var(--text);
  border:1px solid rgba(255,255,255,.28);
  border-radius:22px;
  box-shadow:var(--shadow);
}
.controlCard{padding:20px 22px 18px;margin-bottom:18px}
.controlHeader{display:flex;align-items:flex-start;justify-content:space-between;gap:14px;margin-bottom:15px}
.controlTitle{font-size:20px;font-weight:950}
.controlDesc{font-size:13px;color:var(--muted);font-weight:800;margin-top:5px}
.formGrid{display:grid;grid-template-columns:1.05fr .9fr .95fr .95fr 1fr auto auto;gap:12px;align-items:end}
.field{display:flex;flex-direction:column;gap:7px;min-width:0}
.field label{font-size:13px;font-weight:900;color:var(--muted)}
select,input{
  width:100%;height:46px;border-radius:13px;border:1px solid var(--line);
  background:#fffdfb;color:var(--text);font-size:15px;font-weight:850;padding:0 13px;outline:none
}
select:focus,input:focus{border-color:#d6ad78;box-shadow:0 0 0 4px rgba(246,179,63,.16)}
button{
  height:46px;border:0;border-radius:13px;padding:0 18px;
  font-family:inherit;font-size:15px;font-weight:950;cursor:pointer;white-space:nowrap;
  transition:.16s transform,.16s filter
}
button:hover{transform:translateY(-1px);filter:brightness(1.02)}
button.primary{background:linear-gradient(180deg,#d41d2c,var(--red-2));color:white;box-shadow:0 8px 16px rgba(146,0,10,.18)}
button.secondary{background:#fffdfb;color:#5b3a36;border:1px solid #e5d5c7}
button.mini{height:36px;font-size:13px;padding:0 12px;border-radius:10px}
.updateBox{
  display:none;margin-top:14px;padding:13px 15px;border-radius:16px;
  background:#fff0d1;border:1px solid #f2c878;color:#704000;font-weight:900
}
.updateActions{display:flex;gap:10px;flex-wrap:wrap;margin-top:10px}
.progressBox{
  display:none;margin-top:14px;padding:15px;border-radius:17px;background:linear-gradient(180deg,#fff8ee,#fff3e4);
  border:1px solid #f0d5ad
}
.progressTop{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-bottom:10px}
.progressTitle{font-size:15px;font-weight:950;color:#733a1e}
.progressSub{font-size:12px;color:var(--muted);font-weight:850}
.progressState{display:inline-flex;align-items:center;gap:8px;padding:8px 12px;border-radius:999px;background:#fff0d7;border:1px solid #f1d4aa;color:#7a3d20;font-size:13px;font-weight:950}
.progressState .dot{width:8px;height:8px;border-radius:50%;background:linear-gradient(180deg,#ffb15e,#df1d2d);box-shadow:0 0 0 4px rgba(223,29,45,.10)}
.progressTrack{height:13px;border-radius:999px;background:#eadbce;overflow:hidden}
.progressBar{height:100%;width:0%;background:linear-gradient(90deg,#ce1b29,#f6b33f);border-radius:999px;transition:width .25s ease}
.progressText{margin-top:9px;font-size:13px;color:#5d3a31;font-weight:900}

.mainGrid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:18px;align-items:stretch}
.panel{padding:20px;min-height:430px;display:flex;flex-direction:column}
.panelHead{display:flex;align-items:flex-start;justify-content:space-between;gap:12px;margin-bottom:15px}
.panelHead h2{margin:0;font-size:26px;font-weight:950;color:var(--text);letter-spacing:.2px}
.panelHead p{display:none}
.panelTag{font-size:12px;font-weight:950;color:#7a3d20;background:#fff0d7;border:1px solid #f1d4aa;border-radius:999px;padding:7px 10px;white-space:nowrap}

.pickStage{
  flex:1;min-height:270px;border-radius:20px;border:1px solid var(--line-2);
  background:
    radial-gradient(circle at 50% 10%,rgba(246,179,63,.16),transparent 34%),
    linear-gradient(180deg,#fffdfb,#fff5eb);
  display:flex;flex-direction:column;align-items:center;justify-content:center;padding:24px;
}
.balls{display:flex;justify-content:center;align-items:center;gap:15px;flex-wrap:wrap;width:100%}
.ball{
  width:78px;height:78px;border-radius:50%;display:flex;align-items:center;justify-content:center;
  color:#15100b;font-size:29px;font-weight:950;
  background:radial-gradient(circle at 34% 24%,#fff9d0 0%,#ffe177 26%,#f3aa31 62%,#b86a00 100%);
  border:2px solid #ffe8a2;box-shadow:inset 0 3px 0 rgba(255,255,255,.5),0 12px 18px rgba(181,105,0,.18)
}
.emptyState{
  width:100%;min-height:96px;border-radius:18px;border:1px dashed #e8d4bf;
  display:grid;place-items:center;color:#a3897f;background:rgba(255,255,255,.55);font-weight:900;text-align:center
}
.summaryChips{display:grid;grid-template-columns:repeat(3,1fr);gap:11px;margin-top:16px}
.chip{background:#fffdfb;border:1px solid var(--line);border-radius:15px;padding:13px;text-align:center}
.chip .k{font-size:12px;color:var(--muted);font-weight:900}
.chip .v{font-size:19px;color:#67231f;font-weight:950;margin-top:5px}

.overviewBody{flex:1;display:flex;flex-direction:column;gap:16px}
.metricGrid{display:grid;grid-template-columns:repeat(3,1fr);gap:12px;align-content:start}
.metric{
  min-height:132px;background:#fffdfb;border:1px solid var(--line);border-radius:17px;
  display:flex;flex-direction:column;justify-content:center;align-items:center;text-align:center;padding:15px 13px
}
.metric .label{font-size:16px;color:var(--text);font-weight:950;line-height:1.25}
.metric b{
  display:block;margin:9px 0 7px;font-size:30px;line-height:1.05;
  color:#9f2630;font-weight:950;letter-spacing:.2px
}
.metric .hint{font-size:14px;color:var(--muted);font-weight:850;line-height:1.45}
.baseline{
  margin-top:auto;padding:16px 16px;border-radius:16px;background:#fff7ec;border:1px solid #efd7b9;
  color:#5c382f;min-height:94px;display:flex;flex-direction:column;justify-content:center;gap:12px
}
.baselinePlaceholder{font-size:15px;font-weight:850;line-height:1.7;color:#6a4639}
.baselineHeader{font-size:15px;font-weight:950;line-height:1.35;color:#67231f}
.baselineGrid{display:grid;grid-template-columns:1fr 1fr;gap:10px}
.baselineCard{background:rgba(255,255,255,.62);border:1px solid #efd7b9;border-radius:14px;padding:11px 12px;display:flex;flex-direction:column;gap:6px}
.baselineCard .k{font-size:13px;font-weight:950;line-height:1.2;color:#8a4e3d;letter-spacing:.2px}
.baselineCard .v{font-size:15px;font-weight:900;line-height:1.55;color:#5c382f}
.baselineMeta{font-size:13px;font-weight:850;line-height:1.65;color:#866457}
@media (max-width: 1100px){.baselineGrid{grid-template-columns:1fr}}

.analysisGrid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:18px;margin-top:18px;align-items:stretch}
.analysisPanel{padding:20px;min-height:300px;display:flex;flex-direction:column}
.distStage{
  flex:1;min-height:270px;border-radius:20px;border:1px solid var(--line-2);
  background:
    radial-gradient(circle at 50% 10%,rgba(246,179,63,.16),transparent 34%),
    linear-gradient(180deg,#fffdfb,#fff5eb);
  display:flex;flex-direction:column;align-items:center;justify-content:center;padding:24px;margin-top:10px;
}
.distStage.has-data{justify-content:flex-start;align-items:stretch}
.distGrid{display:none;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;width:100%;height:100%;align-content:stretch;grid-auto-rows:minmax(98px,1fr)}
.distItem{background:#fffdfb;border:1px solid var(--line);border-radius:16px;padding:16px 12px;text-align:center;min-height:0;display:flex;flex-direction:column;justify-content:center;align-items:center}
.distItem .label{font-size:17px;color:var(--text);font-weight:950;line-height:1.25}
.distItem b{
  display:block;color:#9f2630;font-size:30px;line-height:1.05;
  margin-top:10px;font-weight:950;letter-spacing:.2px
}
.distEmpty{width:100%;min-height:96px}
.infoList{display:grid;gap:10px;margin-top:10px}
.infoLine{
  min-height:48px;display:flex;align-items:center;justify-content:space-between;gap:12px;
  background:#fffdfb;border:1px solid var(--line);border-radius:14px;padding:10px 13px
}
.infoLine .k{font-size:12px;color:var(--muted);font-weight:900}
.infoLine .v{font-size:13px;color:var(--text);font-weight:950;text-align:right}

@media(max-width:1180px){
  .formGrid{grid-template-columns:repeat(3,minmax(0,1fr))}
  .formGrid button{width:100%}
  .mainGrid,.analysisGrid{grid-template-columns:1fr}
  .panel{min-height:auto}
}
@media(max-width:720px){
  .wrap{padding:18px 14px 30px}
  .topbar{align-items:flex-start;flex-direction:column}
  .brand h1{font-size:24px}
  .formGrid{grid-template-columns:repeat(2,minmax(0,1fr))}
  .metricGrid{grid-template-columns:repeat(2,1fr)}
  .summaryChips{grid-template-columns:1fr}
  .distGrid{grid-template-columns:repeat(3,1fr)}
  .metric .label{font-size:15px}
  .metric b{font-size:28px}
  .metric .hint{font-size:13px}
  .distItem .label{font-size:15px}
  .distItem b{font-size:28px}
  .ball{width:66px;height:66px;font-size:24px}
}
@media(max-width:480px){
  .formGrid,.metricGrid{grid-template-columns:1fr}
  .distGrid{grid-template-columns:repeat(2,1fr)}
}
</style>
</head>
<body>
<div class="wrap">
  <div class="topbar">
    <div class="brand">
      <div class="logo"><div class="logoGrid"><span></span><span></span><span></span><span></span><span></span><span></span></div></div>
      <div>
        <h1>BINGO BINGO 智慧選號工具</h1>
      </div>
    </div>
  </div>

  <section class="card controlCard">
    <div class="controlHeader">
      <div>
        <div class="controlTitle">選號條件</div>
        <div class="controlDesc">設定完成後按「開始選號」，工具會以官方資料進行統計與回測。</div>
      </div>
    </div>

    <div class="formGrid">
      <div class="field"><label for="strategy">策略</label><select id="strategy"><option>保守型</option><option selected>平衡型</option><option>逆向型</option><option>純隨機</option></select></div>
      <div class="field"><label for="count">選號數量</label><select id="count"><option value="3">3顆</option><option value="4">4顆</option><option value="5" selected>5顆</option><option value="10">10顆</option></select></div>
      <div class="field"><label for="sims">回測次數</label><select id="sims"><option value="300">300次</option><option value="1000" selected>1000次</option><option value="10000">10000次</option></select></div>
      <div class="field"><label for="range">號碼區間</label><select id="range"><option value="1-80" selected>01~80</option><option value="1-40">01~40</option><option value="41-80">41~80</option></select></div>
      <div class="field"><label for="lookback">統計週期</label><select id="lookback"><option value="auto" selected>自動最佳</option><option value="50">近50期</option><option value="100">近100期</option><option value="300">近300期</option><option value="500">近500期</option><option value="1000">近1000期</option></select></div>
      <button class="primary" onclick="pick()">開始選號</button>
      <button class="secondary" onclick="sync()">手動更新官方資料</button>
    </div>

    <div id="updateBanner" class="updateBox">
      <div id="updateText"></div>
      <div class="updateActions">
        <button class="mini primary" onclick="sync()">立即更新</button>
        <button class="mini secondary" onclick="dismissUpdate()">先不要</button>
      </div>
    </div>

    <div id="progressWrap" class="progressBox">
      <div class="progressTop">
        <div class="progressTitle" id="progressLabel">進度追蹤</div>
        <div class="progressState" id="status"><span class="dot"></span><span>待命中</span></div>
      </div>
      <div class="progressTrack"><div id="progressBar" class="progressBar"></div></div>
      <div id="progressText" class="progressText">準備中...</div>
    </div>
  </section>

  <div class="mainGrid">
    <section class="card panel">
      <div class="panelHead">
        <div>
          <h2>本次推薦號碼</h2>
        </div>
        <div class="panelTag">Recommendation</div>
      </div>
      <div class="pickStage">
        <div class="balls" id="balls"><div class="emptyState">等待開始選號</div></div>
      </div>
      <div class="summaryChips">
        <div class="chip"><div class="k">目前策略</div><div class="v" id="tagStrategy">平衡型</div></div>
        <div class="chip"><div class="k">號碼區間</div><div class="v" id="tagRange">01~80</div></div>
        <div class="chip"><div class="k">統計週期</div><div class="v" id="tagLookback">自動最佳</div></div>
      </div>
    </section>

    <section class="card panel">
      <div class="panelHead">
        <div>
          <h2>回測總覽</h2>
        </div>
        <div class="panelTag">Backtest</div>
      </div>
      <div class="overviewBody">
        <div class="metricGrid">
          <div class="metric"><div class="label">至少中1顆</div><b id="hit">--</b><div class="hint">和隨機基準比</div></div>
          <div class="metric"><div class="label">中2顆以上</div><b id="ge2">--</b><div class="hint">比單純中1顆更有參考</div></div>
          <div class="metric"><div class="label">中3顆以上</div><b id="ge3">--</b><div class="hint">真正較有價值</div></div>
          <div class="metric"><div class="label">平均命中顆數</div><b id="avg">--</b><div class="hint">每期平均</div></div>
          <div class="metric"><div class="label">粗估回收率</div><b id="ret">--</b><div class="hint">依目前獎金表估算</div></div>
          <div class="metric"><div class="label">最大連敗</div><b id="lose">--</b><div class="hint">連續未回收</div></div>
        </div>
        <div class="baseline" id="baselineBox"><div class="baselinePlaceholder">尚未計算。完成後會比較本次策略與隨機選號的差異。</div></div>
      </div>
    </section>
  </div>

  <div class="analysisGrid">
    <section class="card analysisPanel">
      <div class="panelHead">
        <div>
          <h2>命中分布</h2>
        </div>
        <div class="panelTag">Distribution</div>
      </div>
      <div id="distStage" class="distStage">
        <div class="distGrid" id="distBox"></div>
        <div id="distEmpty" class="emptyState distEmpty">等待開始選號</div>
      </div>
    </section>

    <section class="card analysisPanel">
      <div class="panelHead">
        <div>
          <h2>資料與執行摘要</h2>
        </div>
        <div class="panelTag">Data</div>
      </div>
      <div class="infoList">
        <div class="infoLine"><div class="k">官方資料狀態</div><div class="v" id="infoStatus">等待載入</div></div>
        <div class="infoLine"><div class="k">資料來源</div><div class="v" id="infoSources">--</div></div>
        <div class="infoLine"><div class="k">使用資料筆數</div><div class="v" id="infoRecords">--</div></div>
        <div class="infoLine"><div class="k">獎金表來源</div><div class="v" id="infoPayout">--</div></div>
        <div class="infoLine"><div class="k">最後計算摘要</div><div class="v" id="infoSummary">尚未計算</div></div>
      </div>
    </section>
  </div>
</div>

<script>
function setIdlePlaceholders(){
  document.getElementById('balls').innerHTML='<div class="emptyState">等待開始選號</div>';
  document.getElementById('distEmpty').textContent='等待開始選號';
  document.getElementById('distEmpty').style.display='grid';
  document.getElementById('distBox').style.display='none';
  document.getElementById('distStage').classList.remove('has-data');
}
function setWorkingPlaceholders(){
  document.getElementById('balls').innerHTML='<div class="emptyState">計算中，正在產生推薦號碼...</div>';
  document.getElementById('distEmpty').textContent='計算中，正在整理命中分布...';
  document.getElementById('distEmpty').style.display='grid';
  document.getElementById('distBox').style.display='none';
  document.getElementById('distStage').classList.remove('has-data');
}
function setErrorPlaceholders(){
  document.getElementById('balls').innerHTML='<div class="emptyState">計算失敗，請重新開始</div>';
  document.getElementById('distEmpty').textContent='計算失敗，請重新開始';
  document.getElementById('distEmpty').style.display='grid';
  document.getElementById('distBox').style.display='none';
  document.getElementById('distStage').classList.remove('has-data');
}
function renderBalls(nums){
  const b=document.getElementById('balls');
  b.innerHTML='';
  if(!nums || !nums.length){
    b.innerHTML='<div class="emptyState">等待開始選號</div>';
    return;
  }
  nums.forEach(n=>{
    const d=document.createElement('div');
    d.className='ball';
    d.textContent=String(n).padStart(2,'0');
    b.appendChild(d);
  });
}
function renderDistribution(dist){
  const box=document.getElementById('distBox');
  const empty=document.getElementById('distEmpty');
  const stage=document.getElementById('distStage');
  box.innerHTML='';
  const keys=Object.keys(dist||{});
  if(!keys.length){
    empty.style.display='grid';
    box.style.display='none';
    box.style.gridTemplateColumns='repeat(3, minmax(0,1fr))';
    stage.classList.remove('has-data');
    return;
  }
  empty.style.display='none';
  box.style.display='grid';
  stage.classList.add('has-data');
  const n=keys.length;
  let cols=3;
  if(n<=2) cols=2;
  else if(n<=4) cols=2;
  else if(n<=6) cols=3;
  else if(n<=9) cols=3;
  else cols=4;
  box.style.gridTemplateColumns=`repeat(${cols}, minmax(0,1fr))`;
  keys.sort((a,b)=>Number(a)-Number(b)).forEach(k=>{
    const d=document.createElement('div');
    d.className='distItem';
    d.innerHTML=`<div class="label">中 ${k} 顆</div><b>${dist[k]}%</b>`;
    box.appendChild(d);
  });
}
function dismissUpdate(){ document.getElementById('updateBanner').style.display='none'; }
function showUpdate(text){ document.getElementById('updateText').textContent=text; document.getElementById('updateBanner').style.display='block'; }
function setQuickTags(){
  document.getElementById('tagStrategy').textContent=document.getElementById('strategy').value;
  document.getElementById('tagRange').textContent=document.getElementById('range').selectedOptions[0].textContent;
  document.getElementById('tagLookback').textContent=document.getElementById('lookback').selectedOptions[0].textContent;
}
async function loadDataStatus(){
  const st=document.querySelector('#status span:last-child');
  const infoStatus=document.getElementById('infoStatus');
  const payoutEl=document.getElementById('infoPayout');
  payoutEl.textContent='官方獎金表同步中';
  try{
    const r=await fetch('/data-status');
    const j=await r.json();
    if(j.payout){
      const pSource = j.payout.source || '未同步｜官方基準表';
      const pBet = j.payout.bet_amount || 25;
      const pState = j.payout.ok ? '｜已同步' : '';
      payoutEl.textContent=`${pSource}｜每注 ${pBet} 元${pState}`;
    }
    if(!j.has_cache){
      st.textContent='第一次使用：尚未建立官方資料，正在自動同步...';
      infoStatus.textContent='首次啟用，自動同步中';
      await sync(true);
      return;
    }
    const y=j.cached_year ? `｜資料年度：${j.cached_year}` : '';
    const t=j.updated_at ? `｜快取更新：${j.updated_at}` : '';
    st.textContent=`${j.message}${y}${t}`;
    infoStatus.textContent=j.message + (j.cached_year ? `（年度 ${j.cached_year}）` : '');
    document.getElementById('infoSummary').textContent='可直接開始選號';
    setTimeout(checkOfficialUpdate, 300);
  }catch(e){
    st.textContent='資料狀態檢查失敗，可先嘗試手動更新官方資料。';
    infoStatus.textContent='資料狀態檢查失敗';
  }
}
async function checkOfficialUpdate(){
  try{
    const r=await fetch('/update-check?force=1');
    const j=await r.json();
    if(j.update_available){
      const ly=j.latest_official && j.latest_official.year ? j.latest_official.year : '最新';
      const cy=j.cached_year || '未知';
      showUpdate(`發現官方有較新的資料：目前快取年度 ${cy}，官方可下載年度 ${ly}。可手動更新。`);
    }else if(j.checked_remote){
      const summary=document.getElementById('infoSummary');
      if(summary && summary.textContent==='可直接開始選號') summary.textContent='已檢查官方更新';
    }
  }catch(e){}
}
async function sync(auto=false){
  const st=document.querySelector('#status span:last-child');
  dismissUpdate();
  st.textContent=auto ? '第一次自動同步官方資料中...' : '官方資料更新中...';
  document.getElementById('infoStatus').textContent=auto ? '首次同步中' : '官方資料更新中';
  showProgress(3, '下載官方索引與年度資料...');
  const r=await fetch('/sync?force=1');
  const j=await r.json();
  st.textContent=j.message || JSON.stringify(j);
  if(j.ok){
    const y=j.cached_year ? `｜資料年度：${j.cached_year}` : '';
    const t=j.updated_at ? `｜更新時間：${j.updated_at}` : '';
    st.textContent=`${j.message}${y}${t}`;
    document.getElementById('infoStatus').textContent=j.message + (j.cached_year ? `（年度 ${j.cached_year}）` : '');
    if(j.payout){
      const pSource = j.payout.source || '未同步｜官方基準表';
      const pBet = j.payout.bet_amount || 25;
      const pState = j.payout.ok ? '｜已同步' : '';
      document.getElementById('infoPayout').textContent=`${pSource}｜每注 ${pBet} 元${pState}`;
    }else{
      await loadDataStatus();
    }
    showProgress(100, '官方資料更新完成');
    hideProgressSoon();
  }else{
    document.getElementById('infoStatus').textContent='官方資料更新失敗';
    showProgress(100, j.message || '官方資料更新失敗');
  }
}
function showProgress(percent, text){
  document.getElementById('progressWrap').style.display='block';
  document.getElementById('progressBar').style.width=percent+'%';
  document.getElementById('progressText').textContent=text;
}
function hideProgressSoon(){ setTimeout(()=>{document.getElementById('progressWrap').style.display='none';}, 1200); }
async function pick(){
  setQuickTags();
  const payload={
    count:Number(document.getElementById('count').value),
    strategy:document.getElementById('strategy').value,
    sims:Number(document.getElementById('sims').value),
    number_range:document.getElementById('range').value,
    lookback:document.getElementById('lookback').value
  };
  const st=document.querySelector('#status span:last-child');
  st.textContent='已建立計算任務，準備開始...';
  document.getElementById('infoSummary').textContent='建立計算任務中';
  setWorkingPlaceholders();
  showProgress(1,'準備中...');
  const startResp=await fetch('/pick/start',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});
  const started=await startResp.json();
  if(!started.ok){ st.textContent=started.message || '建立任務失敗'; document.getElementById('infoSummary').textContent='建立任務失敗'; setErrorPlaceholders(); showProgress(0, started.message || '建立任務失敗'); return; }
  const jobId=started.job_id;
  const startedAt=Date.now();
  const timer=setInterval(async()=>{
    const r=await fetch('/pick/status/'+jobId);
    const j=await r.json();
    const elapsed=Math.max(1, Math.round((Date.now()-startedAt)/1000));
    const percent=Number(j.percent || 0);
    let etaText='';
    if(percent > 3 && percent < 100){
      const eta=Math.max(1, Math.round(elapsed * (100 - percent) / percent));
      const etaMin=Math.floor(eta/60);
      const etaSec=eta%60;
      etaText = etaMin > 0 ? `｜預估剩約 ${etaMin}分${etaSec}秒` : `｜預估剩約 ${etaSec}秒`;
    }else if(percent > 0 && percent < 100){ etaText='｜預估中'; }
    showProgress(percent, `${j.stage || '計算中'} ${j.detail || ''}｜已耗時 ${elapsed} 秒${etaText}`);
    st.textContent=j.stage || '計算中...';
    document.getElementById('infoSummary').textContent=(j.stage || '計算中...') + (j.detail ? `｜${j.detail}` : '');
    if(j.done){
      clearInterval(timer);
      if(!j.ok){ st.textContent=j.message || '計算失敗'; document.getElementById('infoSummary').textContent='計算失敗'; setErrorPlaceholders(); showProgress(100, j.message || '計算失敗'); return; }
      const res=j.result;
      renderBalls(res.numbers);
      document.getElementById('hit').textContent=res.backtest.hit_rate+'%';
      document.getElementById('ge2').textContent=res.backtest.ge2_rate+'%';
      document.getElementById('ge3').textContent=res.backtest.ge3_rate+'%';
      document.getElementById('avg').textContent=res.backtest.avg_hits;
      document.getElementById('ret').textContent=res.backtest.return_rate+'%';
      document.getElementById('lose').textContent=res.backtest.max_losing_streak;
      renderDistribution(res.backtest.hit_distribution || {});
      const rb=res.backtest.random_baseline || {};
      const vrh=res.backtest.vs_random_hit_rate || 0;
      const vrr=res.backtest.vs_random_return_rate || 0;
      const lb=res.lookback_used ? `統計週期：近 ${res.lookback_used} 期` : '';
      const payoutText=res.payout ? `獎金表：${res.payout.source || '未同步｜官方基準表'}` : '';
      document.getElementById('baselineBox').innerHTML=`
        <div class="baselineHeader">這次結果和隨機選號相比</div>
        <div class="baselineGrid">
          <div class="baselineCard">
            <div class="k">隨機選號</div>
            <div class="v">至少中1顆 ${rb.hit_rate}%<br>中3顆以上 ${rb.ge3_rate}%<br>回收率 ${rb.return_rate}%</div>
          </div>
          <div class="baselineCard">
            <div class="k">這次策略</div>
            <div class="v">命中率 ${vrh>=0?'+':''}${vrh}%<br>回收率 ${vrr>=0?'+':''}${vrr}%</div>
          </div>
        </div>
        <div class="baselineMeta">${lb}${lb && payoutText ? '｜' : ''}${payoutText}</div>`;
      if(res.payout){
        const pSource = res.payout.source || '未同步｜官方基準表';
        const pBet = res.payout.bet_amount || 25;
        const pState = res.payout.ok ? '｜已同步' : '';
        document.getElementById('infoPayout').textContent=`${pSource}｜每注 ${pBet} 元${pState}`;
      }
      st.textContent=`計算完成：使用官方資料 ${res.records} 筆；來源：${res.sources.join('、')}${lb}`;
      document.getElementById('infoSources').textContent=res.sources.join('、') || '--';
      document.getElementById('infoRecords').textContent=String(res.records || '--');
      document.getElementById('infoSummary').textContent=`計算完成｜${payload.strategy}｜${payload.count}顆${lb}`;
      showProgress(100, `完成｜共耗時 ${elapsed} 秒`);
      hideProgressSoon();
    }
  }, 350);
}
window.addEventListener('load', ()=>{ setQuickTags(); setIdlePlaceholders(); loadDataStatus(); });
document.getElementById('strategy').addEventListener('change', setQuickTags);
document.getElementById('range').addEventListener('change', setQuickTags);
document.getElementById('lookback').addEventListener('change', setQuickTags);
</script>
</body>
</html>
"""



def _parse_lookback_value(value: Any, default: int = 300) -> Any:
    if value is None:
        return default
    if isinstance(value, str) and value.lower().strip() == "auto":
        return "auto"
    try:
        return max(20, int(value))
    except Exception:
        return default


def _run_pick_job(job_id: str, payload: Dict[str, Any]) -> None:
    started = time.time()
    try:
        count = int(payload.get("count", 5))
        strategy = str(payload.get("strategy", "平衡型"))
        sims = int(payload.get("sims", 300))
        lookback_raw = _parse_lookback_value(payload.get("lookback", "auto"), default=300)
        number_range = str(payload.get("number_range", "1-80"))
        weekday_filter = bool(payload.get("weekday_filter", False))

        _job_update(job_id, 5, "讀取官方索引資料", "確認快取與官方歷史資料", eta_seconds=6)
        sync_result = sync_official_data(force=False)
        data = [r["numbers"] for r in sync_result["records"]]
        if weekday_filter:
            data = filter_weekday(data)

        eta = _estimate_seconds(len(data), sims)
        if lookback_raw == "auto" and strategy != "純隨機":
            _job_update(job_id, 18, "尋找最佳統計週期", "快速測試 50/100/300/500/1000 期", eta_seconds=eta)
            def lb_cb(done, total, lb):
                pct = 18 + int(14 * done / max(1, total))
                _job_update(job_id, pct, "尋找最佳統計週期", f"測試近 {lb} 期 ({done}/{total})", eta_seconds=eta)
            opt = optimize_lookback(data, count=count, strategy=strategy, number_range=number_range, progress_cb=lb_cb)
            lookback = int(opt.get("best_lookback", 300))
            lookback_info = opt
        else:
            lookback = 300 if lookback_raw == "auto" else int(lookback_raw)
            lookback_info = {"best_lookback": lookback, "results": [], "quick_sims": 0}

        _job_update(job_id, 34, "建立統計權重", f"官方資料 {len(data)} 筆｜統計週期：近 {lookback} 期", eta_seconds=eta)
        scores = build_scores(data, strategy=strategy, lookback=lookback)
        payout_summary = get_payout_summary(force=False)
        payout_table = get_payout_table(force=False)

        total_rounds = min(max(30, sims), max(30, len(data)-30))
        _job_update(job_id, 42, "回測中", f"準備回測 {total_rounds} 次", eta_seconds=eta)
        def cb(done, total):
            pct = 42 + int(56 * done / max(1, total))
            _job_update(job_id, pct, "回測中", f"{done}/{total} 次｜統計週期：近 {lookback} 期", eta_seconds=eta)

        nums = pick_numbers(scores, count=count, number_range=number_range)
        bt = backtest(data, count=count, strategy=strategy, sims=sims, lookback=lookback, number_range=number_range, progress_cb=cb, payout_table=payout_table)

        result = {
            "ok": True,
            "numbers": nums,
            "weekday": _dt.datetime.now().strftime("%A"),
            "records": sync_result["record_count"],
            "used_records": len(data),
            "strategy": strategy,
            "lookback_used": lookback,
            "lookback_auto": lookback_raw == "auto",
            "lookback_info": lookback_info,
            "sources": [Path(s).name for s in sync_result.get("sources", [])],
            "payout": payout_summary,
            "backtest": bt,
        }
        _job_update(job_id, 100, "計算完成", "推薦號碼與回測結果已更新", done=True, ok=True, result=result, elapsed_seconds=round(time.time()-started, 2))
    except Exception as e:
        _log(f"選號任務失敗：{e}")
        _job_update(job_id, 100, "計算失敗", str(e), done=True, ok=False, message=f"選號失敗：{e}", elapsed_seconds=round(time.time()-started, 2))

@app.route("/")
def index():
    return render_template_string(HTML)



@app.route("/data-status")
def data_status_route():
    # 首頁只回傳本機快取狀態；若沒有獎金表快取，才建立一次官方獎金表快取。
    # 官方開獎資料是否有新版，交給 /update-check 做輕量檢查，不在這裡下載大檔。
    payout = get_payout_summary(force=not _payout_cache_is_official())
    return jsonify({"ok": True, **get_local_cache_summary(), "payout": payout})


@app.route("/payout-sync", methods=["GET", "POST"])
def payout_sync_route():
    try:
        return jsonify({"ok": True, "payout": get_payout_summary(force=True)})
    except Exception as e:
        _log(f"獎金表同步失敗：{e}")
        return jsonify({"ok": False, "message": f"獎金表同步失敗：{e}", "payout": get_payout_summary(force=False)}), 500


@app.route("/update-check")
def update_check_route():
    force = request.args.get("force", "1") == "1"
    return jsonify(check_official_update_available(force=force))


@app.route("/sync", methods=["GET", "POST"])
def sync_route():
    try:
        data = get_data()

        return jsonify({
            "ok": True,
            "message": f"✅ API資料取得成功，共 {len(data)} 筆",
            "records": len(data),
            "from_cache": False,
        })
    except Exception as e:
        return jsonify({
            "ok": False,
            "message": f"❌ API讀取失敗: {str(e)}"
        }), 500
	


@app.route("/pick/start", methods=["POST"])
def pick_start():
    payload = request.get_json(silent=True) or {}
    job_id = uuid.uuid4().hex
    with JOBS_LOCK:
        JOBS[job_id] = {
            "ok": True,
            "done": False,
            "percent": 0,
            "stage": "排入計算",
            "detail": "等待背景計算開始",
            "created_at": time.time(),
            "updated_at": time.time(),
            "eta_seconds": _estimate_seconds(300, int(payload.get("sims", 300) or 300)),
        }
    t = threading.Thread(target=_run_pick_job, args=(job_id, payload), daemon=True)
    t.start()
    return jsonify({"ok": True, "job_id": job_id})


@app.route("/pick/status/<job_id>")
def pick_status(job_id: str):
    job = _job_get(job_id)
    if not job:
        return jsonify({"ok": False, "done": True, "percent": 100, "stage": "找不到任務", "message": "任務不存在或已清除"}), 404
    return jsonify(job)


@app.route("/pick", methods=["POST"])
def pick():
    payload = request.get_json(silent=True) or {}
    count = int(payload.get("count", 5))
    strategy = str(payload.get("strategy", "平衡型"))
    sims = int(payload.get("sims", 300))
    lookback_raw = _parse_lookback_value(payload.get("lookback", "auto"), default=300)
    number_range = str(payload.get("number_range", "1-80"))
    weekday_filter = bool(payload.get("weekday_filter", False))

    try:
        sync_result = sync_official_data(force=False)
        data = [r["numbers"] for r in sync_result["records"]]
        if weekday_filter:
            data = filter_weekday(data)

        if lookback_raw == "auto" and strategy != "純隨機":
            opt = optimize_lookback(data, count=count, strategy=strategy, number_range=number_range)
            lookback = int(opt.get("best_lookback", 300))
        else:
            opt = {"best_lookback": 300 if lookback_raw == "auto" else int(lookback_raw), "results": [], "quick_sims": 0}
            lookback = int(opt["best_lookback"])

        scores = build_scores(data, strategy=strategy, lookback=lookback)
        nums = pick_numbers(scores, count=count, number_range=number_range)
        payout_summary = get_payout_summary(force=False)
        payout_table = get_payout_table(force=False)
        bt = backtest(data, count=count, strategy=strategy, sims=sims, lookback=lookback, number_range=number_range, payout_table=payout_table)

        return jsonify({
            "ok": True,
            "numbers": nums,
            "weekday": _dt.datetime.now().strftime("%A"),
            "records": sync_result["record_count"],
            "used_records": len(data),
            "strategy": strategy,
            "lookback_used": lookback,
            "lookback_auto": lookback_raw == "auto",
            "lookback_info": opt,
            "sources": [Path(s).name for s in sync_result.get("sources", [])],
            "payout": payout_summary,
            "backtest": bt,
        })
    except Exception as e:
        _log(f"選號失敗：{e}")
        return jsonify({
            "ok": False,
            "message": f"選號失敗：{e}",
            "hint": "請先執行 /sync?force=1，或檢查 official_cache 是否已有官方資料。",
        }), 500


@app.route("/debug")
def debug_route():
    return jsonify({"ok": False, "message": "同步診斷已從正式畫面移除。需要維修時再開啟。"}), 404

def _debug_route_disabled():
    files = []
    for p in sorted(CACHE_DIR.glob("*")):
        try:
            files.append({"name": p.name, "size": p.stat().st_size, "mtime": _dt.datetime.fromtimestamp(p.stat().st_mtime).isoformat(timespec="seconds")})
        except Exception:
            pass

    log_text = ""
    if DEBUG_LOG.exists():
        try:
            log_text = DEBUG_LOG.read_text(encoding="utf-8")[-8000:]
        except Exception:
            log_text = ""

    index_preview = None
    if INDEX_CACHE.exists():
        try:
            obj = json.loads(INDEX_CACHE.read_text(encoding="utf-8"))
            index_preview = {
                "count": len(obj.get("rows", [])),
                "first_rows": obj.get("rows", [])[:3],
            }
        except Exception as e:
            index_preview = {"error": str(e)}

    history_preview = None
    if HISTORY_CACHE.exists():
        try:
            obj = json.loads(HISTORY_CACHE.read_text(encoding="utf-8"))
            history_preview = {
                "count": len(obj.get("records", [])),
                "first_record": obj.get("records", [None])[0],
                "sources": obj.get("sources", []),
                "updated_at": obj.get("updated_at"),
            }
        except Exception as e:
            history_preview = {"error": str(e)}

    return jsonify({
        "app_dir": str(APP_DIR),
        "cache_dir": str(CACHE_DIR),
        "data_gov_dataset": DATA_GOV_DATASET_URL,
        "data_gov_index_csv": DATA_GOV_INDEX_CSV,
        "taiwan_lottery_download_page": TAIWAN_LOTTERY_RESULT_DOWNLOAD,
        "allow_unverified_official_ssl": ALLOW_UNVERIFIED_OFFICIAL_SSL,
        "bingo_parser_fix": "accept_20_award_numbers_without_game_name",
        "cache_files": files,
        "index_cache": index_preview,
        "history_cache": history_preview,
        "debug_log_tail": log_text,
    })



if __name__ == "__main__":
    import os
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
