(function () {
  "use strict";

  var SVG_NS = "http://www.w3.org/2000/svg";
  var NODE_WIDTH = 146;
  var NODE_HEIGHT = 38;
  var LEVEL_GAP = 58;
  var ROW_GAP = 14;
  var MIN_ZOOM = 0.035;
  var MAX_ZOOM = 5;

  var refs = {
    appShell: document.getElementById("appShell"),
    sidebarToggle: document.getElementById("sidebarToggle"),
    detailToggle: document.getElementById("detailToggle"),
    brandMark: document.getElementById("brandMark"),
    projectName: document.getElementById("projectName"),
    searchInput: document.getElementById("searchInput"),
    sectionFilter: document.getElementById("sectionFilter"),
    typeFilter: document.getElementById("typeFilter"),
    indexMeta: document.getElementById("indexMeta"),
    itemList: document.getElementById("itemList"),
    currentLabel: document.getElementById("currentLabel"),
    currentTitle: document.getElementById("currentTitle"),
    fullGraphButton: document.getElementById("fullGraphButton"),
    focusGraphButton: document.getElementById("focusGraphButton"),
    zoomOutButton: document.getElementById("zoomOutButton"),
    fitButton: document.getElementById("fitButton"),
    zoomInButton: document.getElementById("zoomInButton"),
    mobileGraphButton: document.getElementById("mobileGraphButton"),
    mobileDetailButton: document.getElementById("mobileDetailButton"),
    workspace: document.getElementById("workspace"),
    graphStats: document.getElementById("graphStats"),
    graphViewport: document.getElementById("graphViewport"),
    dependencyGraph: document.getElementById("dependencyGraph"),
    graphScene: document.getElementById("graphScene"),
    graphEmpty: document.getElementById("graphEmpty"),
    legend: document.getElementById("legend"),
    detailContent: document.getElementById("detailContent"),
    fatalError: document.getElementById("fatalError")
  };

  var data = null;
  var project = null;
  var items = [];
  var sections = [];
  var itemById = new Map();
  var sectionById = new Map();
  var orderById = new Map();
  var consumersById = new Map();
  var preferencePrefix = "reasbook-theorem-map";
  var state = {
    selectedId: "",
    graphMode: "full",
    sidebarCollapsed: false,
    detailCollapsed: false,
    mobileView: "graph",
    visibleListIds: [],
    transform: { x: 0, y: 0, scale: 1 },
    graphWidth: 1,
    graphHeight: 1,
    pointer: null
  };

  function svgElement(name, attributes) {
    var element = document.createElementNS(SVG_NS, name);
    Object.keys(attributes || {}).forEach(function (key) {
      element.setAttribute(key, String(attributes[key]));
    });
    return element;
  }

  function readPreference(key) {
    try {
      return window.localStorage.getItem(preferencePrefix + ":" + key);
    } catch (error) {
      return null;
    }
  }

  function writePreference(key, value) {
    try {
      window.localStorage.setItem(preferencePrefix + ":" + key, value);
    } catch (error) {
      // Preferences are optional in private and file contexts.
    }
  }

  function sectionMeta(sectionId) {
    return sectionById.get(sectionId) || {
      id: sectionId,
      label: sectionId || "Overview",
      short: sectionId || "Overview",
      color: "#315fb5",
      wash: "#e9effa"
    };
  }

  function applySectionStyle(element, sectionId) {
    var section = sectionMeta(sectionId);
    element.style.setProperty("--section-color", section.color || "#315fb5");
    element.style.setProperty("--section-wash", section.wash || "#e9effa");
  }

  function selectedItem() {
    return itemById.get(state.selectedId) || items[0] || null;
  }

  function itemSort(leftId, rightId) {
    return (orderById.get(leftId) || 0) - (orderById.get(rightId) || 0);
  }

  function ancestorsOf(startId) {
    var result = new Set();
    var start = itemById.get(startId);
    var stack = start ? start.dependencies.slice() : [];
    while (stack.length) {
      var current = stack.pop();
      if (result.has(current)) {
        continue;
      }
      result.add(current);
      var item = itemById.get(current);
      if (item) {
        item.dependencies.forEach(function (id) { stack.push(id); });
      }
    }
    return result;
  }

  function descendantsOf(startId) {
    var result = new Set();
    var stack = (consumersById.get(startId) || []).slice();
    while (stack.length) {
      var current = stack.pop();
      if (result.has(current)) {
        continue;
      }
      result.add(current);
      (consumersById.get(current) || []).forEach(function (id) { stack.push(id); });
    }
    return result;
  }

  function encodePath(path) {
    return String(path || "")
      .split("/")
      .filter(Boolean)
      .map(function (segment) { return encodeURIComponent(segment); })
      .join("/");
  }

  function sourceUrl(item) {
    var repository = String(project.repository || "").replace(/\/$/, "");
    var sourceRoot = encodePath(project.sourceRoot || "");
    var file = encodePath(item.file || "");
    return repository + "/blob/" + encodeURIComponent(project.branch) + "/" +
      sourceRoot + (sourceRoot ? "/" : "") + file +
      "?plain=1#L" + Number(item.line || 1);
  }

  function moduleName(item) {
    if (item.module) {
      return item.module;
    }
    var suffix = String(item.file || "")
      .replace(/\.lean$/, "")
      .replace(/\//g, ".");
    return project.id + (suffix ? "." + suffix : "");
  }

  function populateFilters() {
    sections.forEach(function (section) {
      var option = document.createElement("option");
      option.value = section.id;
      option.textContent = section.label;
      refs.sectionFilter.appendChild(option);
    });
    Array.from(new Set(items.map(function (item) { return item.type; })))
      .sort()
      .forEach(function (type) {
        var option = document.createElement("option");
        option.value = type.toLowerCase();
        option.textContent = type;
        refs.typeFilter.appendChild(option);
      });
  }

  function renderLegend() {
    var fragment = document.createDocumentFragment();
    sections.slice(0, 8).forEach(function (section) {
      var entry = document.createElement("span");
      var swatch = document.createElement("i");
      swatch.className = "legend-swatch";
      applySectionStyle(swatch, section.id);
      entry.appendChild(swatch);
      entry.appendChild(document.createTextNode(section.short || section.label));
      fragment.appendChild(entry);
    });
    refs.legend.replaceChildren(fragment);
  }

  function listMatches(item) {
    var needle = refs.searchInput.value.trim().toLowerCase();
    var section = refs.sectionFilter.value;
    var type = refs.typeFilter.value;
    if (section !== "all" && item.section !== section) {
      return false;
    }
    if (type !== "all" && item.type.toLowerCase() !== type) {
      return false;
    }
    if (!needle) {
      return true;
    }
    return [
      item.label,
      item.title,
      item.type,
      item.file,
      item.declaration,
      sectionMeta(item.section).label
    ].join(" ").toLowerCase().indexOf(needle) >= 0;
  }

  function renderList() {
    var visible = items.filter(listMatches);
    var fragment = document.createDocumentFragment();
    refs.itemList.replaceChildren();
    state.visibleListIds = visible.map(function (item) { return item.id; });
    refs.indexMeta.textContent = visible.length + " of " + items.length + " literature items";

    if (!visible.length) {
      var empty = document.createElement("div");
      empty.className = "empty-list";
      empty.textContent = "No literature items match the current filters.";
      refs.itemList.appendChild(empty);
      return;
    }

    sections.forEach(function (section) {
      var sectionItems = visible.filter(function (item) {
        return item.section === section.id;
      });
      if (!sectionItems.length) {
        return;
      }
      var heading = document.createElement("div");
      heading.className = "list-section-label";
      heading.textContent = section.label;
      fragment.appendChild(heading);

      sectionItems.forEach(function (item) {
        var row = document.createElement("button");
        row.type = "button";
        row.className = "item-row";
        row.dataset.itemId = item.id;
        row.setAttribute("role", "option");
        row.setAttribute("aria-selected", String(item.id === state.selectedId));
        applySectionStyle(row, item.section);
        if (item.id === state.selectedId) {
          row.classList.add("active");
        }

        var label = document.createElement("span");
        label.className = "item-row-label";
        label.textContent = item.label;
        var copy = document.createElement("span");
        copy.className = "item-row-copy";
        var title = document.createElement("span");
        title.className = "item-row-title";
        title.textContent = item.title;
        var declaration = document.createElement("span");
        declaration.className = "item-row-decl";
        declaration.textContent = item.declaration;
        copy.appendChild(title);
        copy.appendChild(declaration);
        row.appendChild(label);
        row.appendChild(copy);
        fragment.appendChild(row);
      });
    });
    refs.itemList.appendChild(fragment);
  }

  function graphVisibleIds() {
    var section = refs.sectionFilter.value;
    var result = new Set();
    if (state.graphMode === "focus") {
      if (state.selectedId) {
        result.add(state.selectedId);
        ancestorsOf(state.selectedId).forEach(function (id) { result.add(id); });
        descendantsOf(state.selectedId).forEach(function (id) { result.add(id); });
      }
      return Array.from(result).sort(itemSort);
    }
    if (section === "all") {
      return items.map(function (item) { return item.id; });
    }
    items.forEach(function (item) {
      if (item.section === section) {
        result.add(item.id);
        ancestorsOf(item.id).forEach(function (id) { result.add(id); });
      }
    });
    return Array.from(result).sort(itemSort);
  }

  function graphModel(ids) {
    var idSet = new Set(ids);
    var edges = [];
    ids.forEach(function (targetId) {
      var item = itemById.get(targetId);
      item.dependencies.forEach(function (sourceId) {
        if (idSet.has(sourceId)) {
          edges.push({
            source: sourceId,
            target: targetId,
            id: sourceId + "->" + targetId
          });
        }
      });
    });
    return { ids: ids, edges: edges };
  }

  function graphLayout(ids) {
    var idSet = new Set(ids);
    var indegree = new Map();
    var levels = new Map();
    var queue = [];
    ids.forEach(function (id) {
      var item = itemById.get(id);
      var degree = item.dependencies.filter(function (dependency) {
        return idSet.has(dependency);
      }).length;
      indegree.set(id, degree);
      levels.set(id, 0);
      if (!degree) {
        queue.push(id);
      }
    });
    queue.sort(itemSort);
    while (queue.length) {
      var current = queue.shift();
      (consumersById.get(current) || []).forEach(function (consumer) {
        if (!idSet.has(consumer)) {
          return;
        }
        levels.set(consumer, Math.max(levels.get(consumer) || 0, (levels.get(current) || 0) + 1));
        indegree.set(consumer, (indegree.get(consumer) || 1) - 1);
        if (indegree.get(consumer) === 0) {
          queue.push(consumer);
          queue.sort(itemSort);
        }
      });
    }

    var groups = new Map();
    var maximumLevel = 0;
    ids.forEach(function (id) {
      var level = levels.get(id) || 0;
      maximumLevel = Math.max(maximumLevel, level);
      if (!groups.has(level)) {
        groups.set(level, []);
      }
      groups.get(level).push(id);
    });
    groups.forEach(function (group) { group.sort(itemSort); });
    var maximumRows = 1;
    groups.forEach(function (group) { maximumRows = Math.max(maximumRows, group.length); });
    var width = 80 + (maximumLevel + 1) * NODE_WIDTH + maximumLevel * LEVEL_GAP;
    var height = Math.max(390, 70 + maximumRows * NODE_HEIGHT + (maximumRows - 1) * ROW_GAP);
    var positions = new Map();
    groups.forEach(function (group, level) {
      var groupHeight = group.length * NODE_HEIGHT + Math.max(0, group.length - 1) * ROW_GAP;
      var startY = Math.max(35, (height - groupHeight) / 2);
      group.forEach(function (id, row) {
        positions.set(id, {
          x: 40 + level * (NODE_WIDTH + LEVEL_GAP),
          y: startY + row * (NODE_HEIGHT + ROW_GAP)
        });
      });
    });
    return { positions: positions, width: width, height: height };
  }

  function edgePath(source, target) {
    var startX = source.x + NODE_WIDTH;
    var startY = source.y + NODE_HEIGHT / 2;
    var endX = target.x;
    var endY = target.y + NODE_HEIGHT / 2;
    var control = Math.max(30, (endX - startX) * 0.48);
    return "M " + startX + " " + startY + " C " +
      (startX + control) + " " + startY + ", " +
      (endX - control) + " " + endY + ", " + endX + " " + endY;
  }

  function renderGraph(options) {
    var ids = graphVisibleIds();
    var model = graphModel(ids);
    var layout = graphLayout(ids);
    var upstream = ancestorsOf(state.selectedId);
    var downstream = descendantsOf(state.selectedId);
    var edgeLayer = svgElement("g", { class: "edge-layer" });
    var nodeLayer = svgElement("g", { class: "node-layer" });
    refs.graphEmpty.hidden = Boolean(ids.length);

    model.edges.forEach(function (edge) {
      var source = layout.positions.get(edge.source);
      var target = layout.positions.get(edge.target);
      if (!source || !target) {
        return;
      }
      var path = svgElement("path", {
        class: "graph-edge",
        d: edgePath(source, target),
        "data-edge-id": edge.id
      });
      var activeUpstream = upstream.has(edge.source) &&
        (upstream.has(edge.target) || edge.target === state.selectedId);
      var activeDownstream = (edge.source === state.selectedId || downstream.has(edge.source)) &&
        downstream.has(edge.target);
      if (activeUpstream || activeDownstream) {
        path.classList.add("active");
      } else if (state.selectedId) {
        path.classList.add("dim");
      }
      edgeLayer.appendChild(path);
    });

    ids.forEach(function (id) {
      var item = itemById.get(id);
      var position = layout.positions.get(id);
      var node = svgElement("g", {
        class: "graph-node",
        transform: "translate(" + position.x + " " + position.y + ")",
        tabindex: "0",
        role: "button",
        "aria-label": item.label + ": " + item.title,
        "data-node-id": id
      });
      applySectionStyle(node, item.section);
      if (id === state.selectedId) {
        node.classList.add("selected");
      } else if (upstream.has(id)) {
        node.classList.add("upstream");
      } else if (downstream.has(id)) {
        node.classList.add("downstream");
      } else if (state.selectedId) {
        node.classList.add("dim");
      }
      var title = svgElement("title");
      title.textContent = item.label + " - " + item.title;
      var box = svgElement("rect", {
        class: "node-box",
        width: NODE_WIDTH,
        height: NODE_HEIGHT,
        rx: "5",
        ry: "5"
      });
      var label = svgElement("text", {
        class: "node-label",
        x: NODE_WIDTH / 2,
        y: NODE_HEIGHT / 2 + 0.5
      });
      label.textContent = item.label;
      node.appendChild(title);
      node.appendChild(box);
      node.appendChild(label);
      nodeLayer.appendChild(node);
    });

    refs.graphScene.replaceChildren(edgeLayer, nodeLayer);
    state.graphWidth = layout.width;
    state.graphHeight = layout.height;
    refs.graphStats.innerHTML =
      '<span class="stat-pill">' + ids.length + ' nodes</span>' +
      '<span class="stat-pill">' + model.edges.length + ' edges</span>' +
      '<span class="stat-pill">' + (state.graphMode === "focus" ? "neighborhood" : "full graph") + '</span>';
    if (!options || options.fit !== false) {
      window.requestAnimationFrame(fitGraph);
    } else {
      applyTransform();
    }
  }

  function applyTransform() {
    refs.graphScene.setAttribute(
      "transform",
      "translate(" + state.transform.x + " " + state.transform.y + ") " +
        "scale(" + state.transform.scale + ")"
    );
  }

  function fitGraph() {
    var rect = refs.graphViewport.getBoundingClientRect();
    if (rect.width <= 0 || rect.height <= 0) {
      return;
    }
    var scale = Math.min(
      rect.width / Math.max(state.graphWidth, 1),
      rect.height / Math.max(state.graphHeight, 1),
      1.45
    );
    scale = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, scale * 0.92));
    state.transform.scale = scale;
    state.transform.x = (rect.width - state.graphWidth * scale) / 2;
    state.transform.y = (rect.height - state.graphHeight * scale) / 2;
    applyTransform();
  }

  function zoomAt(factor, clientX, clientY) {
    var rect = refs.graphViewport.getBoundingClientRect();
    var pointX = clientX == null ? rect.width / 2 : clientX - rect.left;
    var pointY = clientY == null ? rect.height / 2 : clientY - rect.top;
    var oldScale = state.transform.scale;
    var nextScale = Math.max(MIN_ZOOM, Math.min(MAX_ZOOM, oldScale * factor));
    state.transform.x = pointX - (pointX - state.transform.x) * (nextScale / oldScale);
    state.transform.y = pointY - (pointY - state.transform.y) * (nextScale / oldScale);
    state.transform.scale = nextScale;
    applyTransform();
  }

  function appendInline(parent, text) {
    String(text).split(/(`[^`]*`)/g).forEach(function (part) {
      if (part.length >= 2 && part[0] === "`" && part[part.length - 1] === "`") {
        var code = document.createElement("code");
        code.textContent = part.slice(1, -1);
        parent.appendChild(code);
      } else {
        parent.appendChild(document.createTextNode(part));
      }
    });
  }

  function renderStatement(container, item) {
    if (item.statementHtml) {
      container.innerHTML = item.statementHtml;
      return;
    }
    var statement = String(item.statement || "No natural-language statement is available.").trim();
    var lines = statement.split(/\r?\n/);
    var paragraph = [];
    var list = null;

    function flushParagraph() {
      if (!paragraph.length) {
        return;
      }
      var element = document.createElement("p");
      appendInline(element, paragraph.join(" ").trim());
      container.appendChild(element);
      paragraph = [];
    }

    lines.forEach(function (line) {
      var bullet = line.match(/^\s*[-*]\s+(.+)$/);
      if (bullet) {
        flushParagraph();
        if (!list) {
          list = document.createElement("ul");
          container.appendChild(list);
        }
        var itemElement = document.createElement("li");
        appendInline(itemElement, bullet[1]);
        list.appendChild(itemElement);
        return;
      }
      if (!line.trim()) {
        flushParagraph();
        list = null;
        return;
      }
      list = null;
      paragraph.push(line.trim());
    });
    flushParagraph();
  }

  function relationLink(item) {
    var button = document.createElement("button");
    button.type = "button";
    button.className = "relation-link";
    button.dataset.selectItem = item.id;
    applySectionStyle(button, item.section);
    var dot = document.createElement("span");
    dot.className = "relation-dot";
    var label = document.createElement("span");
    label.className = "relation-label";
    label.textContent = item.label;
    button.appendChild(dot);
    button.appendChild(label);
    return button;
  }

  function relationColumn(title, ids) {
    var column = document.createElement("div");
    column.className = "relation-column";
    var heading = document.createElement("h4");
    heading.textContent = title + " (" + ids.length + ")";
    var list = document.createElement("div");
    list.className = "relation-list";
    if (!ids.length) {
      var empty = document.createElement("div");
      empty.className = "relation-empty";
      empty.textContent = "None at literature level.";
      list.appendChild(empty);
    } else {
      ids.slice().sort(itemSort).forEach(function (id) {
        var item = itemById.get(id);
        if (item) {
          list.appendChild(relationLink(item));
        }
      });
    }
    column.appendChild(heading);
    column.appendChild(list);
    return column;
  }

  function factRow(list, term, description) {
    var dt = document.createElement("dt");
    dt.textContent = term;
    var dd = document.createElement("dd");
    dd.textContent = description;
    list.appendChild(dt);
    list.appendChild(dd);
  }

  function renderDetail() {
    var item = selectedItem();
    if (!item) {
      refs.detailContent.replaceChildren();
      return;
    }
    var header = document.createElement("header");
    header.className = "detail-header";
    var kicker = document.createElement("div");
    kicker.className = "detail-kicker";
    var kind = document.createElement("span");
    kind.className = "detail-kind";
    kind.textContent = item.type;
    var sectionTag = document.createElement("span");
    sectionTag.className = "detail-section-tag";
    sectionTag.textContent = sectionMeta(item.section).short || sectionMeta(item.section).label;
    applySectionStyle(sectionTag, item.section);
    kicker.appendChild(kind);
    kicker.appendChild(sectionTag);
    var heading = document.createElement("h2");
    heading.textContent = item.label;
    var subheading = document.createElement("p");
    subheading.className = "detail-heading";
    subheading.textContent = item.title;
    var source = document.createElement("a");
    source.className = "detail-source-link";
    source.href = sourceUrl(item);
    source.target = "_blank";
    source.rel = "noreferrer";
    var leanMark = document.createElement("span");
    leanMark.className = "lean-mark";
    leanMark.textContent = "LEAN";
    source.appendChild(leanMark);
    source.appendChild(document.createTextNode("Open source at line " + item.line));
    header.appendChild(kicker);
    header.appendChild(heading);
    header.appendChild(subheading);
    header.appendChild(source);

    var statementSection = document.createElement("section");
    statementSection.className = "detail-section";
    var statementHeading = document.createElement("h3");
    statementHeading.textContent = "Natural-language statement";
    var statement = document.createElement("article");
    statement.className = "statement";
    renderStatement(statement, item);
    statementSection.appendChild(statementHeading);
    statementSection.appendChild(statement);

    var relationSection = document.createElement("section");
    relationSection.className = "detail-section";
    var relationHeading = document.createElement("h3");
    relationHeading.textContent = "Literature-level relations";
    var relationGrid = document.createElement("div");
    relationGrid.className = "relation-grid";
    relationGrid.appendChild(relationColumn("Direct dependencies", item.dependencies));
    relationGrid.appendChild(relationColumn("Used directly by", consumersById.get(item.id) || []));
    relationSection.appendChild(relationHeading);
    relationSection.appendChild(relationGrid);

    var leanSection = document.createElement("section");
    leanSection.className = "detail-section";
    var leanHeading = document.createElement("h3");
    leanHeading.textContent = "Lean formalization";
    var facts = document.createElement("dl");
    facts.className = "lean-facts";
    factRow(facts, "Declaration", item.declaration);
    factRow(facts, "Module", moduleName(item));
    factRow(facts, "Source", item.file + ":" + item.line);
    factRow(facts, "Version", project.branch);
    factRow(facts, "Snapshot", String(project.commit || "").slice(0, 10));
    leanSection.appendChild(leanHeading);
    leanSection.appendChild(facts);
    refs.detailContent.replaceChildren(header, statementSection, relationSection, leanSection);
    refs.detailContent.parentElement.scrollTop = 0;
  }

  function renderHeader() {
    var item = selectedItem();
    refs.currentLabel.textContent = item ? item.label : "Theorem map";
    refs.currentTitle.textContent = item ? item.title : project.title;
    refs.fullGraphButton.classList.toggle("active", state.graphMode === "full");
    refs.focusGraphButton.classList.toggle("active", state.graphMode === "focus");
  }

  function selectItem(id, options) {
    if (!itemById.has(id)) {
      return;
    }
    state.selectedId = id;
    if (!options || options.updateHash !== false) {
      window.history.replaceState(null, "", "#" + encodeURIComponent(id));
    }
    renderHeader();
    renderList();
    renderDetail();
    renderGraph({ fit: false });
    if (options && options.mobileDetail && window.innerWidth <= 820) {
      setMobileView("detail");
    }
  }

  function setGraphMode(mode) {
    state.graphMode = mode === "focus" ? "focus" : "full";
    writePreference("graph-mode", state.graphMode);
    renderHeader();
    renderGraph({ fit: true });
  }

  function setSidebarCollapsed(collapsed) {
    state.sidebarCollapsed = Boolean(collapsed);
    refs.appShell.classList.toggle("sidebar-collapsed", state.sidebarCollapsed);
    refs.sidebarToggle.textContent = state.sidebarCollapsed ? ">" : "<";
    refs.sidebarToggle.setAttribute("aria-expanded", String(!state.sidebarCollapsed));
    refs.sidebarToggle.setAttribute("aria-label", state.sidebarCollapsed ? "Expand index" : "Collapse index");
    refs.sidebarToggle.title = state.sidebarCollapsed ? "Expand index" : "Collapse index";
    writePreference("sidebar-collapsed", String(state.sidebarCollapsed));
    window.setTimeout(fitGraph, 170);
  }

  function setDetailCollapsed(collapsed) {
    state.detailCollapsed = Boolean(collapsed);
    refs.appShell.classList.toggle("detail-collapsed", state.detailCollapsed);
    refs.detailToggle.textContent = state.detailCollapsed ? "<" : ">";
    refs.detailToggle.setAttribute("aria-expanded", String(!state.detailCollapsed));
    refs.detailToggle.setAttribute("aria-label", state.detailCollapsed ? "Expand statement" : "Collapse statement");
    refs.detailToggle.title = state.detailCollapsed ? "Expand statement" : "Collapse statement";
    writePreference("detail-collapsed", String(state.detailCollapsed));
    window.setTimeout(fitGraph, 170);
  }

  function setMobileView(view) {
    state.mobileView = view === "detail" ? "detail" : "graph";
    refs.workspace.dataset.mobileView = state.mobileView;
    refs.mobileGraphButton.classList.toggle("active", state.mobileView === "graph");
    refs.mobileDetailButton.classList.toggle("active", state.mobileView === "detail");
    if (state.mobileView === "graph") {
      window.requestAnimationFrame(fitGraph);
    }
  }

  function bindEvents() {
    refs.sidebarToggle.addEventListener("click", function () {
      setSidebarCollapsed(!state.sidebarCollapsed);
    });
    refs.detailToggle.addEventListener("click", function () {
      setDetailCollapsed(!state.detailCollapsed);
    });
    refs.searchInput.addEventListener("input", renderList);
    refs.sectionFilter.addEventListener("change", function () {
      renderList();
      renderGraph({ fit: true });
    });
    refs.typeFilter.addEventListener("change", renderList);
    refs.itemList.addEventListener("click", function (event) {
      var row = event.target.closest("[data-item-id]");
      if (row) {
        selectItem(row.dataset.itemId, { mobileDetail: true });
      }
    });
    refs.itemList.addEventListener("keydown", function (event) {
      if (event.key !== "ArrowDown" && event.key !== "ArrowUp") {
        return;
      }
      event.preventDefault();
      if (!state.visibleListIds.length) {
        return;
      }
      var index = state.visibleListIds.indexOf(state.selectedId);
      var direction = event.key === "ArrowDown" ? 1 : -1;
      var next = (Math.max(index, 0) + direction + state.visibleListIds.length) % state.visibleListIds.length;
      selectItem(state.visibleListIds[next], { updateHash: true });
    });
    refs.fullGraphButton.addEventListener("click", function () { setGraphMode("full"); });
    refs.focusGraphButton.addEventListener("click", function () { setGraphMode("focus"); });
    refs.zoomOutButton.addEventListener("click", function () { zoomAt(0.82); });
    refs.zoomInButton.addEventListener("click", function () { zoomAt(1.22); });
    refs.fitButton.addEventListener("click", fitGraph);
    refs.mobileGraphButton.addEventListener("click", function () { setMobileView("graph"); });
    refs.mobileDetailButton.addEventListener("click", function () { setMobileView("detail"); });
    refs.dependencyGraph.addEventListener("click", function (event) {
      var node = event.target.closest("[data-node-id]");
      if (node) {
        selectItem(node.dataset.nodeId, { mobileDetail: false });
      }
    });
    refs.dependencyGraph.addEventListener("keydown", function (event) {
      var node = event.target.closest("[data-node-id]");
      if (node && (event.key === "Enter" || event.key === " ")) {
        event.preventDefault();
        selectItem(node.dataset.nodeId, { mobileDetail: false });
      }
    });
    refs.detailContent.addEventListener("click", function (event) {
      var relation = event.target.closest("[data-select-item]");
      if (relation) {
        selectItem(relation.dataset.selectItem, { mobileDetail: true });
      }
    });
    refs.graphViewport.addEventListener("wheel", function (event) {
      event.preventDefault();
      zoomAt(Math.exp(-event.deltaY * 0.0012), event.clientX, event.clientY);
    }, { passive: false });
    refs.graphViewport.addEventListener("pointerdown", function (event) {
      if (event.target.closest("[data-node-id]")) {
        return;
      }
      event.preventDefault();
      refs.graphViewport.setPointerCapture(event.pointerId);
      refs.graphViewport.classList.add("dragging");
      state.pointer = {
        id: event.pointerId,
        startX: event.clientX,
        startY: event.clientY,
        originX: state.transform.x,
        originY: state.transform.y
      };
    });
    refs.graphViewport.addEventListener("pointermove", function (event) {
      if (!state.pointer || state.pointer.id !== event.pointerId) {
        return;
      }
      state.transform.x = state.pointer.originX + event.clientX - state.pointer.startX;
      state.transform.y = state.pointer.originY + event.clientY - state.pointer.startY;
      applyTransform();
    });
    function endPointer(event) {
      if (!state.pointer || state.pointer.id !== event.pointerId) {
        return;
      }
      state.pointer = null;
      refs.graphViewport.classList.remove("dragging");
      if (refs.graphViewport.hasPointerCapture(event.pointerId)) {
        refs.graphViewport.releasePointerCapture(event.pointerId);
      }
    }
    refs.graphViewport.addEventListener("pointerup", endPointer);
    refs.graphViewport.addEventListener("pointercancel", endPointer);
    refs.graphViewport.addEventListener("dblclick", fitGraph);
    window.addEventListener("hashchange", function () {
      var id = decodeURIComponent(window.location.hash.replace(/^#/, ""));
      if (itemById.has(id) && id !== state.selectedId) {
        selectItem(id, { updateHash: false });
      }
    });
    var resizeTimer = null;
    window.addEventListener("resize", function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(fitGraph, 100);
    });
  }

  function validateAndLoad(payload) {
    if (!payload || payload.schemaVersion !== 1 || !payload.project || !Array.isArray(payload.items)) {
      throw new Error("data.json does not match theorem-map schema version 1.");
    }
    data = payload;
    project = data.project;
    preferencePrefix += ":" + String(project.id || "project");
    items = data.items.map(function (item) {
      return Object.assign({}, item, {
        dependencies: Array.isArray(item.dependencies) ? item.dependencies.slice() : []
      });
    });
    sections = Array.isArray(data.sections) ? data.sections.slice() : [];
    if (!sections.length) {
      Array.from(new Set(items.map(function (item) { return item.section || "overview"; })))
        .forEach(function (id, index) {
          var palette = [
            ["#315fb5", "#e9effa"], ["#23745d", "#e4f2ed"],
            ["#a14d3d", "#f8eae6"], ["#9a6a12", "#fbf1d8"]
          ][index % 4];
          sections.push({ id: id, label: id, short: id, color: palette[0], wash: palette[1] });
        });
    }
    sections.forEach(function (section) { sectionById.set(section.id, section); });
    items.forEach(function (item, index) {
      item.section = item.section || (sections[0] && sections[0].id) || "overview";
      itemById.set(item.id, item);
      orderById.set(item.id, index);
      consumersById.set(item.id, []);
    });
    items.forEach(function (item) {
      item.dependencies = item.dependencies.filter(function (dependency) {
        return itemById.has(dependency) && dependency !== item.id;
      });
      item.dependencies.forEach(function (dependency) {
        consumersById.get(dependency).push(item.id);
      });
    });
  }

  function initialize() {
    document.title = project.title + " - Theorem Map";
    refs.projectName.textContent = project.title;
    refs.brandMark.textContent = String(project.id || "RB")
      .split(/[_\s-]+/)
      .filter(Boolean)
      .slice(0, 2)
      .map(function (part) { return part[0].toUpperCase(); })
      .join("") || "RB";
    populateFilters();
    renderLegend();
    var hashId = decodeURIComponent(window.location.hash.replace(/^#/, ""));
    state.selectedId = itemById.has(hashId) ? hashId : (items[0] ? items[0].id : "");
    var savedMode = readPreference("graph-mode");
    state.graphMode = savedMode === "focus" || (items.length > 320 && savedMode !== "full")
      ? "focus" : "full";
    state.sidebarCollapsed = readPreference("sidebar-collapsed") === "true";
    state.detailCollapsed = readPreference("detail-collapsed") === "true";
    setSidebarCollapsed(state.sidebarCollapsed);
    setDetailCollapsed(state.detailCollapsed);
    setMobileView("graph");
    bindEvents();
    renderHeader();
    renderList();
    renderDetail();
    renderGraph({ fit: true });
  }

  fetch("./data.json", { cache: "no-cache" })
    .then(function (response) {
      if (!response.ok) {
        throw new Error("Could not load data.json (HTTP " + response.status + ").");
      }
      return response.json();
    })
    .then(function (payload) {
      validateAndLoad(payload);
      initialize();
    })
    .catch(function (error) {
      refs.fatalError.hidden = false;
      refs.fatalError.textContent = "The theorem map could not start.\n\n" + error.message;
    });
}());
