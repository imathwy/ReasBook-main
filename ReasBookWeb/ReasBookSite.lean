import VersoBlog
import ReasBookSite.Home
import ReasBookSite.LiterateModule
import ReasBookSite.Sections
import ReasBookSite.RouteTable
import Book

open Verso Genre Blog Site Syntax
open ReasBookSite.RouteTable
open scoped ReasBookSite.RouteTable

open Output Html Template Theme

def siteRoot : String := "/ReasBook-main/"
def siteRootScript : String := s!"window.__versoSiteRoot=\"{siteRoot}\""
def sidebarDataScript : String := s!"window.__reasbookSidebarData={ReasBookSite.Sections.sidebarDataJson};"
def sidebarFallbackScript : String := r##"
(function () {
  const siteRoot = "/ReasBook-main/";
  const siteRootNoSlash = "/ReasBook-main";

  function trimSlashes(s) {
    return (s || "").replace(/^\/+|\/+$/g, "");
  }

  function canonicalRelPath(rel) {
    rel = (rel || "").replace(/^\/+/, "");
    const keys = ["books/", "papers/", "docs/"];
    for (const key of keys) {
      const i = rel.lastIndexOf(key);
      if (i > 0) return rel.slice(i);
    }
    return rel;
  }

  function currentRelPath() {
    let p = window.location.pathname || "";
    if (p.startsWith(siteRoot)) p = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) p = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) p = p.slice(1);
    return canonicalRelPath(p);
  }

  function findCurrentWork(navData) {
    const rel = currentRelPath();
    const parts = rel.split("/").filter(Boolean);
    if (parts.length >= 2 && parts[0] === "books") {
      const slug = parts[1];
      const work = (navData.books || []).find((w) => w.slug === slug) || null;
      return { kind: "book", work: work };
    }
    if (parts.length >= 2 && parts[0] === "papers") {
      const slug = parts[1];
      const work = (navData.papers || []).find((w) => w.slug === slug) || null;
      return { kind: "paper", work: work };
    }
    if (parts.length >= 3 && parts[0] === "docs" && parts[1] === "Books") {
      const slug = String(parts[2] || "").toLowerCase();
      const work = (navData.books || []).find((w) => String(w.slug || "").toLowerCase() === slug) || null;
      return { kind: "book", work: work };
    }
    if (parts.length >= 3 && parts[0] === "docs" && parts[1] === "Papers") {
      const slug = String(parts[2] || "").toLowerCase();
      const work = (navData.papers || []).find((w) => String(w.slug || "").toLowerCase() === slug) || null;
      return { kind: "paper", work: work };
    }
    return { kind: "", work: null };
  }

  function escapeHtml(s) {
    return String(s || "")
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
  }

  function itemHtml(href, label) {
    return '<li><a href="' + href + '">' + escapeHtml(label) + '</a></li>';
  }

  function fallbackHtml() {
    const navData = window.__reasbookSidebarData || { books: [], papers: [] };
    const current = findCurrentWork(navData);
    let html = "<ol>";
    html += itemHtml(siteRoot, "Home");
    html += itemHtml(siteRoot + "docs/", "Documentation");

    if (current.work) {
      html += "<li><details open><summary>" + escapeHtml(current.work.title) + "</summary><ul>";
      if (current.work.home) {
        html += itemHtml(siteRoot + trimSlashes(current.work.home) + "/", "Home");
      }
      for (const s of (current.work.sections || [])) {
        html += itemHtml(siteRoot + trimSlashes(s.route) + "/", s.title || "");
      }
      html += "</ul></details></li>";
      html += "</ol>";
      return html;
    }

    for (const w of (navData.books || [])) {
      if (w.home) html += itemHtml(siteRoot + trimSlashes(w.home) + "/", w.title || "Book");
    }
    for (const w of (navData.papers || [])) {
      if (w.home) html += itemHtml(siteRoot + trimSlashes(w.home) + "/", w.title || "Paper");
    }
    html += "</ol>";
    return html;
  }

  function ensureSidebarFallback() {
    var navRoot = document.getElementById("sidebar-nav-root");
    if (!navRoot) return;
    if (navRoot.children && navRoot.children.length > 0) return;
    navRoot.innerHTML = fallbackHtml();
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", ensureSidebarFallback);
  else ensureSidebarFallback();
})();
"##
def docsRoot : String := s!"{siteRoot}docs/"
def staticRoot : String := s!"{siteRoot}static/style.css"
def navLinkRewriteScript : String := r##"
(function () {
  const siteRoot = "/ReasBook-main/";
  const siteRootNoSlash = "/ReasBook-main";
  const specials = ["#", "mailto:", "tel:"];

  function isSpecial(href) {
    return specials.some((p) => href.startsWith(p));
  }

  function trimToLastSegment(rel, key) {
    const i = rel.lastIndexOf(key);
    if (i > 0) return rel.slice(i);
    return rel;
  }

  function canonicalRelPath(rel) {
    rel = rel.replace(/^\/+/, "");
    rel = trimToLastSegment(rel, "books/");
    rel = trimToLastSegment(rel, "papers/");
    rel = trimToLastSegment(rel, "docs/");
    return rel;
  }

  function currentRelPath() {
    let p = window.location.pathname || "";
    if (p.startsWith(siteRoot)) p = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) p = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) p = p.slice(1);
    return canonicalRelPath(p);
  }

  function findCurrentWork(navData) {
    const rel = currentRelPath();
    const parts = rel.split("/").filter(Boolean);
    if (parts.length >= 2 && parts[0] === "books") {
      const slug = parts[1];
      const work = (navData.books || []).find((w) => w.slug === slug) || null;
      return { kind: "book", work: work };
    }
    if (parts.length >= 2 && parts[0] === "papers") {
      const slug = parts[1];
      const work = (navData.papers || []).find((w) => w.slug === slug) || null;
      return { kind: "paper", work: work };
    }
    if (parts.length >= 3 && parts[0] === "docs" && parts[1] === "Books") {
      const slug = String(parts[2] || "").toLowerCase();
      const work = (navData.books || []).find((w) => String(w.slug || "").toLowerCase() === slug) || null;
      return { kind: "book", work: work };
    }
    if (parts.length >= 3 && parts[0] === "docs" && parts[1] === "Papers") {
      const slug = String(parts[2] || "").toLowerCase();
      const work = (navData.papers || []).find((w) => String(w.slug || "").toLowerCase() === slug) || null;
      return { kind: "paper", work: work };
    }
    return { kind: "", work: null };
  }

  function normalizeInternalHref(href) {
    if (!href) return href;
    href = href.trim();
    if (!href || isSpecial(href)) return href;

    let u;
    try {
      u = new URL(href, window.location.origin);
    } catch (_) {
      return href;
    }

    if (u.origin !== window.location.origin) return href;

    // Preserve query/hash while normalizing the path component.
    const qh = u.search + u.hash;
    let p = u.pathname;

    if (p === "/" || p === "/index.html") return siteRoot + qh;
    if (p === "/docs" || p === "/docs/") return siteRoot + "docs/" + qh;

    let rel;
    if (p.startsWith(siteRoot)) rel = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) rel = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) rel = p.slice(1);
    else rel = p;

    rel = canonicalRelPath(rel);
    return siteRoot + rel + qh;
  }

  function rewriteAllAnchors() {
    for (const a of document.querySelectorAll("a[href]")) {
      const oldHref = (a.getAttribute("href") || "").trim();
      const newHref = normalizeInternalHref(oldHref);
      if (newHref && newHref !== oldHref) a.setAttribute("href", newHref);
    }
  }

  function onClick(ev) {
    if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    const a = ev.target && ev.target.closest ? ev.target.closest("a[href]") : null;
    if (!a) return;
    if ((a.getAttribute("target") || "").toLowerCase() === "_blank") return;

    const oldHref = (a.getAttribute("href") || "").trim();
    const newHref = normalizeInternalHref(oldHref);
    if (!newHref || newHref === oldHref) return;

    a.setAttribute("href", newHref);
    ev.preventDefault();
    window.location.assign(newHref);
  }

  function boot() {
    const navData = window.__reasbookSidebarData || { books: [], papers: [] };
    const navRoot = document.getElementById("sidebar-nav-root");

    function trimSlashes(s) {
      return (s || "").replace(/^\/+|\/+$/g, "");
    }

    function mkItem(href, label) {
      const li = document.createElement("li");
      const a = document.createElement("a");
      a.href = href;
      a.textContent = label;
      li.appendChild(a);
      return li;
    }

    function mkWorkDetails(work) {
      const li = document.createElement("li");
      const details = document.createElement("details");
      details.open = true;
      const summary = document.createElement("summary");
      summary.textContent = work.title;
      details.appendChild(summary);

      const sectionList = document.createElement("ul");
      if (work.home) {
        sectionList.appendChild(mkItem(siteRoot + trimSlashes(work.home) + "/", "Home"));
      }
      for (const s of (work.sections || [])) {
        sectionList.appendChild(mkItem(siteRoot + trimSlashes(s.route) + "/", s.title));
      }
      details.appendChild(sectionList);
      li.appendChild(details);
      return li;
    }

    function mkSectionGroup(title, works) {
      const li = document.createElement("li");
      const details = document.createElement("details");
      details.open = true;
      const summary = document.createElement("summary");
      summary.textContent = title;
      details.appendChild(summary);

      const workList = document.createElement("ul");
      for (const w of works || []) {
        workList.appendChild(mkWorkDetails(w));
      }

      details.appendChild(workList);
      li.appendChild(details);
      return li;
    }

    function renderGroupedNav(list) {
      list.appendChild(mkItem(siteRoot, "Home"));
      list.appendChild(mkItem(siteRoot + "docs/", "Documentation"));
      const current = findCurrentWork(navData);
      if (current.work) {
        list.appendChild(mkWorkDetails(current.work));
        return;
      }
      list.appendChild(mkSectionGroup("Books", navData.books || []));
      list.appendChild(mkSectionGroup("Papers", navData.papers || []));
    }

    function renderSidebarNav() {
      if (!navRoot) return;
      const list = document.createElement("ol");
      try {
        renderGroupedNav(list);
      } catch (err) {
        console.error("Failed to build sidebar navigation", err);
        return;
      }
      navRoot.innerHTML = "";
      navRoot.appendChild(list);
    }

    renderSidebarNav();
    rewriteAllAnchors();
    document.addEventListener("click", onClick, true);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})();
"##

def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <base href="/ReasBook-main/"/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href="/ReasBook-main/static/style.css"/>
          <script>{{Html.text false siteRootScript}}</script>
          <script>{{Html.text false sidebarDataScript}}</script>
          <script>{{Html.text false navLinkRewriteScript}}</script>
          <script>{{Html.text false sidebarFallbackScript}}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation" id="sidebar-nav-root"></nav>
            </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
}
|>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

/-- Generated section routes are injected by `reasbook_site_dir` from `ReasBookSite.RouteTable`. -/
def demoSite : Site := reasbook_site

def baseUrl := "https://imathwy.github.io/ReasBook-main/docs/"

def linkTargets : Code.LinkTargets α where
  const name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
  definition name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
where
  mkLink href := { shortDescription := "doc", description := "API documentation", href }

def main := blogMain theme demoSite (linkTargets := linkTargets)
