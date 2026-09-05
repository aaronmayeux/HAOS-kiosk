#!/usr/bin/env python3
# ============================================================================
# THE WALL - kiosk_overlay.py  (the injected browser chrome)
# ----------------------------------------------------------------------------
# Chromium here runs with --kiosk: no address bar, no tabs, no back button, no
# bookmark UI. This watcher supplies all of it, injected into the live page over
# CDP. Because Runtime.evaluate runs in a debugger context it bypasses the
# page's CSP, so the toolbar mounts on sites that forbid framing -- which is why
# there is no iframe anywhere in this feature.
#
# WHAT IT INJECTS: a fixed 58px top bar -- back / forward / reload / address bar
# / GO / bookmark star / bookmarks / WALL / collapse. Never on the Wall
# dashboard itself (the script self-suppresses on DASH_URL), so the card's frame
# budget is untouched.
#
# HOW IT MOUNTS (two paths, belt and braces):
#   1. Page.addScriptToEvaluateOnNewDocument -- armed once per session, runs at
#      document-start on EVERY navigation, so the bar is there before the page
#      paints. No flash, no polling gap.
#   2. A 1s Runtime.evaluate drain that also re-mounts if the bar is missing
#      (covers the already-loaded page at startup and any target reset).
#
# BOOKMARKS: the injected star and the bookmark home page both push
# {op:"add"|"del", url, title} onto window.__WALL_BM_Q. The 1s drain empties
# that queue, merges it, and persists ONE full list through Home Assistant's
# shell_command.bookmarks_write (-> /config/bookmarks_write.py ->
# /config/www/browser/bookmarks.json, served at /local/browser/bookmarks.json).
# Reading is a plain GET of that same file. The add-on needs no extra config
# mapping: it writes through HA, not through the filesystem.
#
# Standard library only. Self-healing: any exception drops the CDP session and
# reconnects a second later.
# ============================================================================
import base64
import json
import os
import socket
import struct
import time
import urllib.request

HA    = os.environ.get("HA_URL", "http://127.0.0.1:8123").rstrip("/")
DASH  = os.environ.get("HA_DASHBOARD", "").lstrip("/")
PORT  = int(os.environ.get("REMOTE_DEBUG_PORT", "9222"))
TOKEN = os.environ.get("SUPERVISOR_TOKEN", "")

DASH_URL = HA + "/" + DASH if DASH else HA + "/"
# The launcher face sends the kiosk to the localhost form; match it so the URL
# the bar's bookmarks button uses is byte-identical to the one it lands on.
HOME_URL = HA.replace("127.0.0.1", "localhost") + "/local/browser/home.html"
BM_URL   = HA + "/local/browser/bookmarks.json"
SVC_URL  = "http://supervisor/core/api/services/shell_command/bookmarks_write"

# --------------------------------------------------------------------------- #
# The injected toolbar
# --------------------------------------------------------------------------- #
# Every element is built with createElement + CSSOM (el.style.setProperty), never
# innerHTML with a style attribute: a strict style-src CSP blocks inline style
# ATTRIBUTES but never direct CSSOM writes, so the bar looks right everywhere.
# Lato is not installed in this image, so the stack falls through to Open Sans.
INJECT_TPL = r"""(function(){
  var DASH='%DASH%', HOME='%HOME%', ID='wall-web-bar', PID='wall-web-pill';
  // Suppress ONLY on the Wall dashboard. Anything HA serves out of /local/ (the
  // bookmark home page, the game wrappers) is a kiosk-out page and gets the bar,
  // whichever host form it was reached by.
  function onWall(){
    if(location.pathname.indexOf('/local/')===0) return false;
    return location.href.indexOf(DASH)===0;
  }
  function drop(id){ var e=document.getElementById(id); if(e&&e.parentNode) e.parentNode.removeChild(e); }
  if(onWall()){ drop(ID); drop(PID); return 'wall'; }

  if(!window.__WALL_BM) window.__WALL_BM = %BOOKMARKS%;
  if(!window.__WALL_BM_Q) window.__WALL_BM_Q = [];

  var BARH=64;   // one source: the bar's height AND the page's push-down
  var BG='#0E1116', FG='#FFFFFF', FIELD='#1B2027', KEY='rgba(255,255,255,0.10)';
  var FONT='Lato,"Open Sans","DejaVu Sans",Arial,sans-serif';
  var _bar=null,_pill=null,_star=null,_inp=null;

  function sty(el,css){ for(var k in css){ try{ el.style.setProperty(k,css[k],'important'); }catch(e){} } }

  // PUSH-DOWN. The bar is position:fixed, so on its own it would sit ON TOP of
  // the page and hide the first 64px. Padding the root element instead reflows
  // the whole document down by exactly the bar height, so nothing is covered.
  // Caveat worth knowing: an element the page itself positions fixed at top:0
  // is laid out against the viewport, not the root, so a site's own sticky
  // header still slides under the bar. Normal document content -- which is
  // almost everything -- clears it.
  function pad(on){
    try{
      var de=document.documentElement;
      if(!de) return;
      if(on) de.style.setProperty('padding-top', BARH+'px', 'important');
      else   de.style.removeProperty('padding-top');
    }catch(e){}
  }

  function isBm(){
    var u=location.href, a=window.__WALL_BM||[];
    for(var i=0;i<a.length;i++){ if(a[i]&&a[i].url===u) return true; }
    return false;
  }

  // Address-bar normalisation: a scheme goes as-is, a host[:port] gets http://,
  // anything that looks like a domain gets https://, everything else is a search.
  function norm(v){
    v=(v||'').trim();
    if(!v) return '';
    if(/^[a-z][a-z0-9+.-]*:\/\//i.test(v)) return v;
    if(/^about:/i.test(v)) return v;
    if(/^(localhost|\d{1,3}(\.\d{1,3}){3})(:\d+)?([\/?#]|$)/i.test(v)) return 'http://'+v;
    if(/^[^\s\/]+\.[a-z]{2,}([\/?#:]|$)/i.test(v)) return 'https://'+v;
    return 'https://www.google.com/search?q='+encodeURIComponent(v);
  }

  function go(){ var u=norm(_inp?_inp.value:''); if(u) location.href=u; }

  // OUTBOUND SEAM. Nav + bookmark ops leave the page over a CDP binding
  // (Runtime.addBinding -> Runtime.bindingCalled), which reaches the add-on
  // instantly on the socket it already holds. Back/forward are therefore
  // BROWSER-level (Page.navigateToHistoryEntry) and cannot be swallowed by a
  // page's own pushState stack -- the in-page history.back() failure mode.
  // Returns false if the binding isn't up, so callers can fall back.
  function out(o){
    if(typeof window.__wallSend==='function'){
      try{ window.__wallSend(JSON.stringify(o)); return true; }catch(e){}
    }
    return false;
  }
  window.__wallOut=function(o){ try{ return out(o); }catch(e){ return false; } };

  function key(label,w,fs,fn){
    var b=document.createElement('div');
    b.textContent=label;
    sty(b,{flex:'0 0 auto',width:w+'px',height:'48px',display:'flex',
      'align-items':'center','justify-content':'center','font-family':FONT,
      'font-size':fs+'px','font-weight':'700',color:FG,background:KEY,
      cursor:'pointer','user-select':'none','-webkit-user-select':'none',
      '-webkit-tap-highlight-color':'transparent','line-height':'1',
      'border-radius':'0','box-sizing':'border-box','text-transform':'none',
      transition:'transform 80ms ease'});
    var dn=function(){ b.style.setProperty('transform','scale(0.9)','important'); };
    var up=function(){ b.style.setProperty('transform','scale(1)','important'); };
    b.addEventListener('pointerdown',dn);
    b.addEventListener('pointerup',up);
    b.addEventListener('pointerleave',up);
    b.addEventListener('pointercancel',up);
    b.addEventListener('click',function(e){ e.preventDefault(); e.stopPropagation(); try{ fn(); }catch(err){} });
    return b;
  }

  function build(){
    var bar=document.createElement('div');
    bar.id=ID;
    sty(bar,{position:'fixed',top:'0',left:'0',right:'0',width:'100%',height:BARH+'px',
      'z-index':'2147483647',background:BG,display:'flex','align-items':'center',
      gap:'7px',padding:'0 20px',margin:'0','box-sizing':'border-box',
      'box-shadow':'0 2px 12px rgba(0,0,0,0.55)','font-family':FONT});

    bar.appendChild(key('\u2039',68,34,function(){ if(!out({op:'back'})) history.back(); }));
    bar.appendChild(key('\u203A',68,34,function(){ if(!out({op:'forward'})) history.forward(); }));
    bar.appendChild(key('\u21BB',68,26,function(){ location.reload(); }));

    var inp=document.createElement('input');
    inp.type='text'; inp.id=ID+'-url';
    inp.setAttribute('autocomplete','off');
    inp.setAttribute('autocorrect','off');
    inp.setAttribute('autocapitalize','off');
    inp.setAttribute('spellcheck','false');
    inp.value=location.href;
    sty(inp,{flex:'1 1 auto','min-width':'0',height:'48px',background:FIELD,color:FG,
      border:'0',outline:'none','font-family':FONT,'font-size':'20px','font-weight':'400',
      padding:'0 14px',margin:'0','box-sizing':'border-box','border-radius':'0',
      'letter-spacing':'0'});
    // Focus is what makes Onboard auto-show; select-all so typing replaces.
    inp.addEventListener('focus',function(){ setTimeout(function(){ try{ inp.select(); }catch(e){} },0); });
    inp.addEventListener('keydown',function(e){
      if(e.key==='Enter'||e.keyCode===13){ e.preventDefault(); e.stopPropagation(); go(); }
    });
    bar.appendChild(inp); _inp=inp;

    bar.appendChild(key('GO',76,18,go));

    _star=key('\u2606',68,28,function(){
      var u=location.href, t=((document.title||u)+'').slice(0,80);
      var a=window.__WALL_BM||[], op;
      if(isBm()){
        window.__WALL_BM=a.filter(function(b){ return b.url!==u; });
        op={op:'del',url:u};
      } else {
        window.__WALL_BM=a.concat([{title:t,url:u}]);
        op={op:'add',url:u,title:t};
      }
      // Binding first (instant); the 1s queue is only the fallback path.
      if(!out(op)) window.__WALL_BM_Q.push(op);
      sync();
    });
    _star.id=ID+'-star';
    bar.appendChild(_star);

    // A hamburger reads as "menu"; this page is a GRID of saved tiles, so the
    // squared glyph says what it opens. Star stays the save action.
    bar.appendChild(key('\u229E',68,30,function(){ location.href=HOME; }));
    bar.appendChild(key('WALL',96,17,function(){ location.href=DASH; }));
    bar.appendChild(key('\u00BB',52,22,function(){ collapse(true); }));

    var pill=document.createElement('div');
    pill.id=PID;
    pill.textContent='\u00AB WEB';
    sty(pill,{position:'fixed',top:'0',right:'0','z-index':'2147483647',background:BG,
      color:FG,'font-family':FONT,'font-size':'15px','font-weight':'700',
      'letter-spacing':'0.10em',padding:'10px 16px',cursor:'pointer',
      'user-select':'none','-webkit-tap-highlight-color':'transparent',
      display:'none','box-shadow':'0 2px 10px rgba(0,0,0,0.55)'});
    pill.addEventListener('click',function(e){ e.preventDefault(); e.stopPropagation(); collapse(false); });

    _bar=bar; _pill=pill;
    return {bar:bar,pill:pill};
  }

  function collapse(on){
    if(!_bar||!_pill) return;
    _bar.style.setProperty('display', on?'none':'flex','important');
    _pill.style.setProperty('display', on?'block':'none','important');
    pad(!on);   // collapsed -> give the page its 64px back
  }

  // Re-adopt refs: the script can run twice in one document (doc-start arm, then
  // a drain re-eval), and the second closure starts with null element vars.
  function adopt(){
    _bar=document.getElementById(ID);
    _pill=document.getElementById(PID);
    _inp=document.getElementById(ID+'-url');
    _star=document.getElementById(ID+'-star');
  }

  function sync(){
    if(!_bar) adopt();
    // Re-assert the push-down: a page's own scripts can rewrite the root style.
    if(_bar && _bar.style.display!=='none'){
      var de=document.documentElement;
      if(de && de.style.paddingTop !== BARH+'px') pad(true);
    }
    if(_star){
      var on=isBm();
      _star.textContent = on ? '\u2605' : '\u2606';
      _star.style.setProperty('color', on ? '#FFC400' : FG, 'important');
    }
    if(_inp && document.activeElement!==_inp && _inp.value!==location.href){
      _inp.value=location.href;
    }
  }

  function mount(){
    if(onWall()){ drop(ID); drop(PID); pad(false); return true; }
    if(document.getElementById(ID)){ sync(); return true; }
    var root=document.body||document.documentElement;
    if(!root) return false;
    var b=build();
    root.appendChild(b.bar);
    root.appendChild(b.pill);
    pad(true);
    sync();
    return true;
  }

  window.__wallMount=function(){ try{ return mount(); }catch(e){ return false; } };
  window.__wallSync=function(){ try{ sync(); }catch(e){} };

  if(!window.__wallMount()){
    if(document.readyState==='loading'){
      document.addEventListener('DOMContentLoaded',function(){ window.__wallMount(); });
    }
    var n=0, iv=setInterval(function(){
      if(window.__wallMount() || ++n>50) clearInterval(iv);
    },100);
  }
  return 'ok';
})();"""

# Drains the in-page bookmark queue AND re-mounts if the bar went missing.
# Returns a JSON string: {q:[...], m:1|0, u:"<href>"}. m=0 means the toolbar
# script never ran in this document, so the poller re-injects it whole.
DRAIN_JS = r"""(function(){
  var q=window.__WALL_BM_Q||[]; window.__WALL_BM_Q=[];
  var m=0;
  if(typeof window.__wallMount==='function'){ try{ window.__wallMount(); }catch(e){} m=1; }
  return JSON.stringify({q:q,m:m,u:location.href});
})();"""


def inject(bms):
    return (INJECT_TPL
            .replace("%DASH%", DASH_URL)
            .replace("%HOME%", HOME_URL)
            .replace("%BOOKMARKS%", json.dumps(bms)))


# --------------------------------------------------------------------------- #
# Bookmark store (read over HTTP, write through HA's shell_command)
# --------------------------------------------------------------------------- #
def load_bms():
    try:
        with urllib.request.urlopen(BM_URL + "?t=%d" % time.time(), timeout=5) as r:
            d = json.loads(r.read().decode("utf-8"))
        b = d.get("bookmarks") if isinstance(d, dict) else d
        if not isinstance(b, list):
            return []
        return [x for x in b if isinstance(x, dict) and x.get("url")][:60]
    except Exception:
        return []


def save_bms(bms):
    if not TOKEN:
        raise RuntimeError("no SUPERVISOR_TOKEN")
    b64 = base64.b64encode(json.dumps(bms).encode("utf-8")).decode("ascii")
    req = urllib.request.Request(
        SVC_URL,
        data=json.dumps({"b64": b64}).encode("utf-8"),
        method="POST",
        headers={"Authorization": "Bearer " + TOKEN,
                 "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=10) as r:
        r.read()


# --------------------------------------------------------------------------- #
# Minimal CDP websocket client (persistent, timeout-tolerant)
# --------------------------------------------------------------------------- #
def recvn(s, n):
    b = b""
    while len(b) < n:
        c = s.recv(n - len(b))
        if not c:
            break
        b += c
    return b


def ws_connect(path):
    s = socket.create_connection(("127.0.0.1", PORT), timeout=5)
    k = base64.b64encode(os.urandom(16)).decode()
    s.sendall((f"GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{PORT}\r\nUpgrade: websocket\r\n"
               f"Connection: Upgrade\r\nSec-WebSocket-Key: {k}\r\n"
               f"Sec-WebSocket-Version: 13\r\n\r\n").encode())
    r = b""
    while b"\r\n\r\n" not in r:
        c = s.recv(4096)
        if not c:
            raise RuntimeError("handshake closed")
        r += c
    return s


def ws_send(s, obj):
    d = json.dumps(obj).encode()
    n = len(d)
    m = os.urandom(4)
    h = bytearray([0x81])
    if n < 126:
        h.append(0x80 | n)
    elif n < 65536:
        h.append(0x80 | 126); h += struct.pack(">H", n)
    else:
        h.append(0x80 | 127); h += struct.pack(">Q", n)
    h += m
    s.sendall(bytes(h) + bytes(b ^ m[i % 4] for i, b in enumerate(d)))


def ws_recv(s, first_timeout):
    """('text',str) | ('ping'|'other'|'timeout','') | ('close','') | None."""
    s.settimeout(first_timeout)
    try:
        b0 = s.recv(1)
    except socket.timeout:
        return ("timeout", "")
    except OSError:
        return None
    if not b0:
        return None
    s.settimeout(8)                       # mid-frame: read it out or drop the session
    op = b0[0] & 0x0F
    b1 = recvn(s, 1)
    if not b1:
        return None
    l = b1[0] & 0x7F
    if l == 126:
        l = struct.unpack(">H", recvn(s, 2))[0]
    elif l == 127:
        l = struct.unpack(">Q", recvn(s, 8))[0]
    p = recvn(s, l)
    if op == 0x8:
        return ("close", "")
    if op == 0x9:
        return ("ping", "")
    if op != 0x1:
        return ("other", "")
    return ("text", p.decode("utf-8", "replace"))


def page_target():
    ts = json.load(urllib.request.urlopen("http://127.0.0.1:%d/json" % PORT, timeout=3))
    p = next((t for t in ts if t.get("type") == "page"), None)
    if not p:
        return None, None
    return p.get("id", ""), p.get("webSocketDebuggerUrl", "")


# --------------------------------------------------------------------------- #
# Session
# --------------------------------------------------------------------------- #
def session():
    tid, wsurl = page_target()
    if not wsurl:
        raise RuntimeError("no page target")

    bms = load_bms()
    s = ws_connect(wsurl.split(str(PORT), 1)[1])
    try:
        nid = [0]
        pend = {}
        script_id = [None]

        def send(method, params=None, tag=None):
            nid[0] += 1
            ws_send(s, {"id": nid[0], "method": method, "params": params or {}})
            if tag:
                pend[nid[0]] = tag
            return nid[0]

        def arm(current):
            send("Page.addScriptToEvaluateOnNewDocument", {"source": inject(current)}, "arm")

        send("Page.enable")
        # Runtime is needed for the binding; it also makes every console.log an
        # event, so the read loop prefilters before parsing (see below).
        send("Runtime.enable")
        send("Runtime.addBinding", {"name": "__wallSend"})
        arm(bms)
        send("Runtime.evaluate", {"expression": inject(bms), "returnByValue": True})
        print("[overlay] session up (target %s, %d bookmark(s))" % (tid, len(bms)), flush=True)

        last = 0.0
        while True:
            msg = ws_recv(s, 0.4)
            if msg is None or msg[0] == "close":
                raise RuntimeError("cdp socket closed")
            if msg[0] == "text":
                t = msg[1]
                # Prefilter: with Runtime enabled a chatty page floods console
                # events. Only our own replies and our binding are worth parsing.
                if t.startswith('{"id":') or '"Runtime.bindingCalled"' in t:
                    try:
                        o = json.loads(t)
                    except Exception:
                        o = None
                    if o is not None:
                        if o.get("method") == "Runtime.bindingCalled":
                            bms = on_binding(o, bms, send, arm, script_id)
                        elif o.get("id") in pend:
                            tag = pend.pop(o["id"])
                            if tag == "arm":
                                script_id[0] = (o.get("result") or {}).get("identifier")
                            elif tag == "drain":
                                bms = on_drain(o, bms, send, arm, script_id)
                            elif tag in ("nav:back", "nav:forward"):
                                step_history(o, tag, send)

            now = time.time()
            if now - last >= 1.0:
                last = now
                t2, _ = page_target()
                if t2 != tid:
                    raise RuntimeError("page target changed")
                send("Runtime.evaluate", {"expression": DRAIN_JS, "returnByValue": True}, "drain")
    finally:
        try:
            s.close()
        except Exception:
            pass


def on_drain(o, bms, send, arm, script_id):
    val = (((o.get("result") or {}).get("result")) or {}).get("value")
    if not val:
        send("Runtime.evaluate", {"expression": inject(bms), "returnByValue": True})
        return bms
    try:
        d = json.loads(val)
    except Exception:
        return bms

    if not d.get("m"):                    # toolbar script never ran here -> inject
        send("Runtime.evaluate", {"expression": inject(bms), "returnByValue": True})

    q = d.get("q") or []
    if not q:
        return bms

    return apply_bm(bms, q, send, arm, script_id)


def apply_bm(bms, ops, send, arm, script_id):
    """Merge add/del ops, persist ONE full list, push it back into the page.

    Shared by both inbound paths: the instant CDP binding and the 1s queue
    drain. One merge, one write, one definition of the store.
    """
    changed = False
    for a in ops:
        if not isinstance(a, dict):
            continue
        op = a.get("op")
        u = (a.get("url") or "").strip()
        if not u.startswith(("http://", "https://")):
            continue
        if op == "add":
            if not any(b.get("url") == u for b in bms):
                bms = bms + [{"title": ((a.get("title") or u) + "")[:80],
                              "url": u,
                              "added": int(time.time() * 1000)}]
                changed = True
        elif op == "del":
            n = [b for b in bms if b.get("url") != u]
            if len(n) != len(bms):
                bms = n
                changed = True

    if changed:
        try:
            save_bms(bms)
            print("[overlay] bookmarks: %d saved" % len(bms), flush=True)
        except Exception as e:
            print("[overlay] bookmark save failed:", e, flush=True)
        # Push the merged list into the live page, then re-arm document-start
        # so the next navigation carries it too.
        send("Runtime.evaluate", {
            "expression": "window.__WALL_BM=" + json.dumps(bms) +
                          ";window.__wallSync&&window.__wallSync();"})
        if script_id[0]:
            send("Page.removeScriptToEvaluateOnNewDocument", {"identifier": script_id[0]})
            script_id[0] = None
        arm(bms)
    return bms


def on_binding(o, bms, send, arm, script_id):
    """window.__wallSend(json) from the toolbar -- nav ops and bookmark ops."""
    p = o.get("params") or {}
    if p.get("name") != "__wallSend":
        return bms
    try:
        d = json.loads(p.get("payload") or "{}")
    except Exception:
        return bms
    op = d.get("op")
    if op == "back":
        send("Page.getNavigationHistory", None, "nav:back")
    elif op == "forward":
        send("Page.getNavigationHistory", None, "nav:forward")
    elif op in ("add", "del"):
        return apply_bm(bms, [d], send, arm, script_id)
    return bms


def step_history(o, tag, send):
    """Browser-level back/forward -- steps the REAL entry list, so a page's own
    pushState stack can't absorb the tap the way history.back() lets it."""
    r = o.get("result") or {}
    entries = r.get("entries") or []
    i = r.get("currentIndex")
    if i is None:
        return
    j = i - 1 if tag == "nav:back" else i + 1
    if 0 <= j < len(entries):
        send("Page.navigateToHistoryEntry", {"entryId": entries[j].get("id")})


def main():
    for _ in range(60):                   # wait for the debug port on cold boot
        try:
            if page_target()[1]:
                break
        except Exception:
            pass
        time.sleep(1)
    while True:
        try:
            session()
        except Exception as e:
            print("[overlay] session ended: %s" % e, flush=True)
        time.sleep(1)


if __name__ == "__main__":
    main()
