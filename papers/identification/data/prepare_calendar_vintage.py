"""Extract the meeting schedule from the preserved 30 March 2026 Fed snapshot."""
from pathlib import Path
from datetime import datetime
import csv, hashlib, json, re

ROOT = Path(__file__).resolve().parent
PATH = ROOT/'raw'/'fomc_calendar_near_2026-03-30.html'
URL = 'https://web.archive.org/web/20260330083005id_/https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm'

def main():
    text = PATH.read_text(encoding='utf-8-sig')
    rows = []
    sections = re.split(r'(<h4><a id="\d+">\d{4} FOMC Meetings</a></h4>)', text)
    for i in range(1,len(sections),2):
        year = int(re.search(r'(\d{4}) FOMC',sections[i]).group(1))
        if year not in [2026,2027]: continue
        pattern = r'fomc-meeting__month[^>]*><strong>([^<]+)</strong></div>\s*<div class="fomc-meeting__date[^>]*>([^<]+)</div>'
        matches = re.findall(pattern, sections[i+1])
        assert len(matches)==8, (year,matches)
        for month, days in matches:
            day = int(re.findall(r'\d+',days)[-1])
            date = datetime.strptime(f'{year} {month} {day}', '%Y %B %d').date().isoformat()
            rows.append(dict(meeting_date=date, scheduled_days_raw=days,
                archive_capture_utc='2026-03-30T08:30:05Z',
                status='scheduled as of archive capture; future dates tentative',source_url=URL))
    assert len(rows)==16
    with (ROOT/'processed'/'fomc_meetings_asof_2026-03-30.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    current={r['decision_date'] for r in csv.DictReader((ROOT/'processed'/'fomc_meetings.csv').open())}
    summary=dict(source_url=URL, html_sha256=hashlib.sha256(PATH.read_bytes()).hexdigest(),
        compressed_response_sha256=hashlib.sha256(PATH.with_suffix('.html.gz').read_bytes()).hexdigest(),
        scheduled_dates=len(rows), dates_not_in_september_calendar=[r['meeting_date'] for r in rows if r['meeting_date'] not in current])
    (ROOT/'processed'/'fomc_vintage_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
