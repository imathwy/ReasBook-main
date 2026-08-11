(function () {
  "use strict";

  var LEAN_REF = "v4.32.2";
  var LEAN_COMMIT = "094e974c4fc99a750543e63051f95b85ad2f92d2";
  var LEAN_BASE =
    "https://github.com/optpku/ReasBook/blob/" +
    LEAN_REF +
    "/ReasBook/Papers/TR_LALM_theory/";

  var ITEMS = [
    {
      id: "assumption-2-1",
      label: "Assumption 2.1",
      title: "Smoothness and uniform LICQ",
      type: "Assumption",
      section: "deterministic",
      file: "Assumption_2_1/Regularity.lean",
      line: 34,
      declaration: "EqualityConstrained.Regularity",
      dependencies: []
    },
    {
      id: "definition-2-2",
      label: "Definition 2.2",
      title: "Approximate KKT point and pair",
      type: "Definition",
      section: "deterministic",
      file: "Definition_2_2/KKT.lean",
      line: 31,
      declaration: "KKT.IsApproximatePair",
      dependencies: ["assumption-2-1"]
    },
    {
      id: "algorithm-2-1",
      label: "Algorithm 2.1",
      title: "Fixed-penalty NR-LALM",
      type: "Algorithm",
      section: "deterministic",
      file: "Algorithm_2_1/Iteration.lean",
      line: 143,
      declaration: "LALM.Run",
      dependencies: ["assumption-2-1"]
    },
    {
      id: "assumption-2-3",
      label: "Assumption 2.3",
      title: "Fixed safe parameter regime",
      type: "Assumption",
      section: "deterministic",
      file: "Assumption_2_3.lean",
      line: 174,
      declaration: "LALM.Parameters",
      dependencies: ["algorithm-2-1"]
    },
    {
      id: "proposition-2-4",
      label: "Proposition 2.4",
      title: "Feasibility of fixed parameters",
      type: "Proposition",
      section: "deterministic",
      file: "Proposition_2_4.lean",
      line: 381,
      declaration: "LALM.existsParametersOfLargeBeta",
      dependencies: ["assumption-2-3"]
    },
    {
      id: "assumption-2-5",
      label: "Assumption 2.5",
      title: "Deterministic localization buffer",
      type: "Assumption",
      section: "deterministic",
      file: "Assumption_2_5/Region.lean",
      line: 78,
      declaration: "LALM.DeterministicRegionCondition",
      dependencies: ["assumption-2-3"]
    },
    {
      id: "lemma-2-6",
      label: "Lemma 2.6",
      title: "Step-multiplier invariant",
      type: "Lemma",
      section: "deterministic",
      file: "Lemma_2_6.lean",
      line: 373,
      declaration: "LALM.Run.norm_step_le",
      dependencies: ["assumption-2-3"]
    },
    {
      id: "lemma-2-7",
      label: "Lemma 2.7",
      title: "Primal augmented-Lagrangian descent",
      type: "Lemma",
      section: "deterministic",
      file: "Lemma_2_7.lean",
      line: 316,
      declaration: "LALM.Run.augmentedLagrangianDescent",
      dependencies: ["lemma-2-6"]
    },
    {
      id: "lemma-2-8",
      label: "Lemma 2.8",
      title: "Multiplier increment control",
      type: "Lemma",
      section: "deterministic",
      file: "Lemma_2_8.lean",
      line: 286,
      declaration: "LALM.Run.norm_multiplier_succ_sub_sq_le",
      dependencies: ["lemma-2-6"]
    },
    {
      id: "theorem-2-9",
      label: "Theorem 2.9",
      title: "Lyapunov descent",
      type: "Theorem",
      section: "deterministic",
      file: "Theorem_2_9.lean",
      line: 97,
      declaration: "LALM.Run.lyapunovDescent",
      dependencies: ["lemma-2-7", "lemma-2-8"]
    },
    {
      id: "theorem-2-10",
      label: "Theorem 2.10",
      title: "Global deterministic localization",
      type: "Theorem",
      section: "deterministic",
      file: "Theorem_2_10.lean",
      line: 767,
      declaration: "LALM.Run.admissible",
      dependencies: ["assumption-2-5", "theorem-2-9"]
    },
    {
      id: "lemma-2-11",
      label: "Lemma 2.11",
      title: "KKT residual bound",
      type: "Lemma",
      section: "deterministic",
      file: "Lemma_2_11.lean",
      line: 237,
      declaration: "LALM.Run.residual_sq_le",
      dependencies: ["definition-2-2", "lemma-2-6", "lemma-2-8"]
    },
    {
      id: "theorem-2-12",
      label: "Theorem 2.12",
      title: "Deterministic complexity",
      type: "Theorem",
      section: "deterministic",
      file: "Theorem_2_12.lean",
      line: 337,
      declaration: "LALM.Run.expect_residual_sq_le",
      dependencies: ["theorem-2-9", "theorem-2-10", "lemma-2-11"]
    },
    {
      id: "theorem-2-13",
      label: "Theorem 2.13",
      title: "Finite length and convergence",
      type: "Theorem",
      section: "deterministic",
      file: "Theorem_2_13.lean",
      line: 804,
      declaration: "LALM.Run.summableStepAndMultiplierIncrement",
      dependencies: ["lemma-2-7", "lemma-2-8", "theorem-2-10", "lemma-2-11"]
    },
    {
      id: "assumption-3-1",
      label: "Assumption 3.1",
      title: "Stochastic first-order oracle",
      type: "Assumption",
      section: "stochastic",
      file: "Assumption_3_1/Oracle.lean",
      line: 19,
      declaration: "EqualityConstrained.StochasticOracle",
      dependencies: []
    },
    {
      id: "definition-3-2",
      label: "Definition 3.2",
      title: "Stochastic approximate KKT pair",
      type: "Definition",
      section: "stochastic",
      file: "Definition_3_2/Stochastic.lean",
      line: 66,
      declaration: "KKT.Stochastic.IsApproximatePair",
      dependencies: ["definition-2-2"]
    },
    {
      id: "lemma-3-3",
      label: "Lemma 3.3",
      title: "Accumulated SPIDER error",
      type: "Lemma",
      section: "stochastic",
      file: "Lemma_3_3.lean",
      line: 1532,
      declaration: "LALM.StochasticRun.accumulatedGradientErrorMeanSquare_le",
      dependencies: ["assumption-2-3", "assumption-3-1"]
    },
    {
      id: "lemma-3-4",
      label: "Lemma 3.4",
      title: "Step-error coupling",
      type: "Lemma",
      section: "stochastic",
      file: "Lemma_3_4.lean",
      line: 1340,
      declaration: "LALM.StochasticRun.augmentedLagrangianDescent",
      dependencies: ["assumption-2-3", "lemma-3-3"]
    },
    {
      id: "lemma-3-5",
      label: "Lemma 3.5",
      title: "Stochastic KKT residual bound",
      type: "Lemma",
      section: "stochastic",
      file: "Lemma_3_5.lean",
      line: 1265,
      declaration: "LALM.StochasticRun.residual_sq_le",
      dependencies: ["definition-2-2", "assumption-2-3", "assumption-3-1"]
    },
    {
      id: "theorem-3-6",
      label: "Theorem 3.6",
      title: "Direct stochastic oracle complexity",
      type: "Theorem",
      section: "stochastic",
      file: "Theorem_3_6.lean",
      line: 309,
      declaration: "LALM.StochasticRun.UniformOutput.residualMeanSquare_le",
      dependencies: ["definition-3-2", "lemma-3-4", "lemma-3-5"]
    },
    {
      id: "theorem-3-7",
      label: "Theorem 3.7",
      title: "Finite-horizon stochastic localization",
      type: "Theorem",
      section: "stochastic",
      file: "Theorem_3_7.lean",
      line: 5068,
      declaration: "LALM.StochasticRun.Localization.exitProbability_le",
      dependencies: ["lemma-3-4", "theorem-3-6"]
    },
    {
      id: "corollary-3-8",
      label: "Corollary 3.8",
      title: "Safeguarded-restart complexity",
      type: "Corollary",
      section: "stochastic",
      file: "Corollary_3_8.lean",
      line: 2261,
      declaration: "LALM.SafeguardedRestart.isApproximatePair_of_iterationBound",
      dependencies: ["theorem-3-7"]
    },
    {
      id: "proposition-4-1",
      label: "Proposition 4.1",
      title: "Containment of sufficient parameter regions",
      type: "Proposition",
      section: "correction",
      file: "Proposition_4_1.lean",
      line: 537,
      declaration: "LALM.Correction.strictParameterRegion",
      dependencies: ["assumption-2-3"]
    },
    {
      id: "corollary-4-2",
      label: "Corollary 4.2",
      title: "NR-LALM+SOC guarantees",
      type: "Corollary",
      section: "correction",
      file: "Corollary_4_2.lean",
      line: 1836,
      declaration: "LALM.Correction.Run.existsApproximatePair",
      dependencies: [
        "theorem-2-12",
        "theorem-2-13",
        "theorem-3-6",
        "corollary-3-8",
        "proposition-4-1"
      ]
    }
  ];

  var SECTION_META = {
    deterministic: {
      label: "Deterministic analysis",
      short: "Section 2"
    },
    stochastic: {
      label: "Stochastic analysis",
      short: "Section 3"
    },
    correction: {
      label: "Second-order correction",
      short: "Section 4"
    }
  };

  var SVG_NS = "http://www.w3.org/2000/svg";
  var NODE_WIDTH = 132;
  var NODE_HEIGHT = 40;
  var LEVEL_GAP = 62;
  var ROW_GAP = 18;
  var MIN_ZOOM = 0.08;
  var MAX_ZOOM = 5;

  var itemById = new Map();
  var orderById = new Map();
  var consumersById = new Map();

  function readPreference(key) {
    try {
      return window.localStorage.getItem(key);
    } catch (error) {
      return null;
    }
  }

  function writePreference(key, value) {
    try {
      window.localStorage.setItem(key, value);
    } catch (error) {
      // Preferences are optional; private file:// contexts may reject storage.
    }
  }

  ITEMS.forEach(function (item, index) {
    itemById.set(item.id, item);
    orderById.set(item.id, index);
    consumersById.set(item.id, []);
  });

  ITEMS.forEach(function (item) {
    item.dependencies.forEach(function (dependencyId) {
      if (consumersById.has(dependencyId)) {
        consumersById.get(dependencyId).push(item.id);
      }
    });
  });

  var refs = {
    appShell: document.getElementById("appShell"),
    sidebarToggle: document.getElementById("sidebarToggle"),
    detailToggle: document.getElementById("detailToggle"),
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
    graphMessage: document.getElementById("graphMessage"),
    graphEmpty: document.getElementById("graphEmpty"),
    detailContent: document.getElementById("detailContent")
  };

  var hashId = window.location.hash.replace(/^#/, "");
  var savedGraphMode = readPreference("tr-lalm-map:graph-mode");
  var state = {
    selectedId: itemById.has(hashId) ? hashId : "assumption-2-1",
    graphMode: savedGraphMode === "focus" ? "focus" : "full",
    sidebarCollapsed:
      readPreference("tr-lalm-map:sidebar-collapsed") === "true",
    detailCollapsed:
      readPreference("tr-lalm-map:detail-collapsed") === "true",
    mobileView: "graph",
    transform: { x: 0, y: 0, scale: 1 },
    graphWidth: 1,
    graphHeight: 1,
    graphBaseWidth: 1,
    graphBaseHeight: 1,
    graphviz: null,
    graphvizPromise: null,
    vizScriptPromise: null,
    renderToken: 0,
    visibleGraphKey: "",
    visibleListIds: ITEMS.map(function (item) { return item.id; }),
    pointer: null,
    mathQueue: Promise.resolve()
  };

  function svgElement(name, attributes) {
    var element = document.createElementNS(SVG_NS, name);
    Object.keys(attributes || {}).forEach(function (key) {
      element.setAttribute(key, String(attributes[key]));
    });
    return element;
  }

  function itemSort(leftId, rightId) {
    return orderById.get(leftId) - orderById.get(rightId);
  }

  function sourceUrl(item) {
    var encodedPath = item.file
      .split("/")
      .map(function (segment) { return encodeURIComponent(segment); })
      .join("/");
    return LEAN_BASE + encodedPath + "?plain=1#L" + item.line;
  }

  function moduleName(item) {
    return "TR_LALM_theory." +
      item.file.replace(/\.lean$/, "").replace(/\//g, ".");
  }

  function ancestorsOf(startId) {
    var result = new Set();
    var stack = (itemById.get(startId) || { dependencies: [] }).dependencies.slice();

    while (stack.length > 0) {
      var current = stack.pop();
      if (result.has(current)) {
        continue;
      }
      result.add(current);
      var item = itemById.get(current);
      if (item) {
        item.dependencies.forEach(function (dependencyId) {
          stack.push(dependencyId);
        });
      }
    }
    return result;
  }

  function descendantsOf(startId) {
    var result = new Set();
    var stack = (consumersById.get(startId) || []).slice();

    while (stack.length > 0) {
      var current = stack.pop();
      if (result.has(current)) {
        continue;
      }
      result.add(current);
      (consumersById.get(current) || []).forEach(function (consumerId) {
        stack.push(consumerId);
      });
    }
    return result;
  }

  function selectedItem() {
    return itemById.get(state.selectedId) || ITEMS[0];
  }

  function populateTypeFilter() {
    var types = Array.from(new Set(ITEMS.map(function (item) {
      return item.type;
    })));

    types.forEach(function (type) {
      var option = document.createElement("option");
      option.value = type.toLowerCase();
      option.textContent = type;
      refs.typeFilter.appendChild(option);
    });
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

    var haystack = [
      item.label,
      item.title,
      item.type,
      item.file,
      item.declaration,
      SECTION_META[item.section].label
    ].join(" ").toLowerCase();
    return haystack.indexOf(needle) >= 0;
  }

  function renderList() {
    var fragment = document.createDocumentFragment();
    var visible = ITEMS.filter(listMatches);
    var sectionOrder = ["deterministic", "stochastic", "correction"];

    refs.itemList.replaceChildren();
    state.visibleListIds = visible.map(function (item) { return item.id; });
    refs.indexMeta.textContent =
      visible.length + " of " + ITEMS.length + " article items";

    if (visible.length === 0) {
      var empty = document.createElement("div");
      empty.className = "empty-list";
      empty.textContent = "No article items match the current filters.";
      refs.itemList.appendChild(empty);
      return;
    }

    sectionOrder.forEach(function (section) {
      var sectionItems = visible.filter(function (item) {
        return item.section === section;
      });
      if (sectionItems.length === 0) {
        return;
      }

      var heading = document.createElement("div");
      heading.className = "list-section-label";
      heading.textContent = SECTION_META[section].short + " / " +
        SECTION_META[section].label;
      fragment.appendChild(heading);

      sectionItems.forEach(function (item) {
        var row = document.createElement("button");
        row.type = "button";
        row.className = "item-row";
        row.dataset.itemId = item.id;
        row.dataset.section = item.section;
        row.setAttribute("role", "option");
        row.setAttribute("aria-selected", String(item.id === state.selectedId));
        if (item.id === state.selectedId) {
          row.classList.add("active");
        }

        var label = document.createElement("span");
        label.className = "item-row-label";
        label.textContent = item.label.replace(" ", "\n");

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
    var result = new Set();
    var section = refs.sectionFilter.value;

    if (state.graphMode === "focus") {
      result.add(state.selectedId);
      ancestorsOf(state.selectedId).forEach(function (id) { result.add(id); });
      descendantsOf(state.selectedId).forEach(function (id) { result.add(id); });
      return Array.from(result).sort(itemSort);
    }

    if (section === "all") {
      return ITEMS.map(function (item) { return item.id; });
    }

    ITEMS.forEach(function (item) {
      if (item.section === section) {
        result.add(item.id);
        ancestorsOf(item.id).forEach(function (id) { result.add(id); });
      }
    });
    return Array.from(result).sort(itemSort);
  }

  function graphLayout(ids) {
    var idSet = new Set(ids);
    var indegree = new Map();
    var levels = new Map();
    var queue = [];

    ids.forEach(function (id) {
      var item = itemById.get(id);
      var count = item.dependencies.filter(function (dependencyId) {
        return idSet.has(dependencyId);
      }).length;
      indegree.set(id, count);
      levels.set(id, 0);
      if (count === 0) {
        queue.push(id);
      }
    });
    queue.sort(itemSort);

    while (queue.length > 0) {
      var current = queue.shift();
      (consumersById.get(current) || []).forEach(function (consumerId) {
        if (!idSet.has(consumerId)) {
          return;
        }
        levels.set(
          consumerId,
          Math.max(levels.get(consumerId), levels.get(current) + 1)
        );
        indegree.set(consumerId, indegree.get(consumerId) - 1);
        if (indegree.get(consumerId) === 0) {
          queue.push(consumerId);
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

    groups.forEach(function (group) {
      group.sort(itemSort);
    });

    var maximumRows = 1;
    groups.forEach(function (group) {
      maximumRows = Math.max(maximumRows, group.length);
    });

    var width = 80 +
      (maximumLevel + 1) * NODE_WIDTH +
      maximumLevel * LEVEL_GAP;
    var height = Math.max(
      390,
      80 + maximumRows * NODE_HEIGHT + (maximumRows - 1) * ROW_GAP
    );
    var positions = new Map();

    groups.forEach(function (group, level) {
      var groupHeight =
        group.length * NODE_HEIGHT + Math.max(0, group.length - 1) * ROW_GAP;
      var top = (height - groupHeight) / 2;
      group.forEach(function (id, index) {
        positions.set(id, {
          x: 40 + level * (NODE_WIDTH + LEVEL_GAP),
          y: top + index * (NODE_HEIGHT + ROW_GAP)
        });
      });
    });

    return {
      positions: positions,
      width: width,
      height: height
    };
  }

  function edgePath(sourcePosition, targetPosition) {
    var sourceX = sourcePosition.x + NODE_WIDTH;
    var sourceY = sourcePosition.y + NODE_HEIGHT / 2;
    var targetX = targetPosition.x;
    var targetY = targetPosition.y + NODE_HEIGHT / 2;
    var control = Math.max(35, (targetX - sourceX) * 0.45);
    return [
      "M", sourceX, sourceY,
      "C", sourceX + control, sourceY,
      targetX - control, targetY,
      targetX, targetY
    ].join(" ");
  }

  function renderGraphFallback(options) {
    var shouldFit = options && options.fit;
    var ids = graphVisibleIds();
    var idSet = new Set(ids);
    var layout = graphLayout(ids);
    var upstream = ancestorsOf(state.selectedId);
    var downstream = descendantsOf(state.selectedId);
    var pathSet = new Set([state.selectedId]);
    upstream.forEach(function (id) { pathSet.add(id); });
    downstream.forEach(function (id) { pathSet.add(id); });
    var edgeCount = 0;
    var edgeLayer = svgElement("g", { class: "edge-layer" });
    var nodeLayer = svgElement("g", { class: "node-layer" });

    refs.graphScene.replaceChildren();
    refs.graphEmpty.hidden = ids.length > 0;

    ids.forEach(function (targetId) {
      var targetItem = itemById.get(targetId);
      targetItem.dependencies.forEach(function (sourceId) {
        if (!idSet.has(sourceId)) {
          return;
        }
        edgeCount += 1;
        var edge = svgElement("path", {
          class: "graph-edge",
          d: edgePath(layout.positions.get(sourceId), layout.positions.get(targetId)),
          "data-source": sourceId,
          "data-target": targetId
        });

        if (upstream.has(sourceId) &&
            (upstream.has(targetId) || targetId === state.selectedId)) {
          edge.classList.add("upstream");
        } else if ((sourceId === state.selectedId || downstream.has(sourceId)) &&
            downstream.has(targetId)) {
          edge.classList.add("downstream");
        } else if (!pathSet.has(sourceId) || !pathSet.has(targetId)) {
          edge.classList.add("dim");
        }
        edgeLayer.appendChild(edge);
      });
    });

    ids.forEach(function (id) {
      var item = itemById.get(id);
      var position = layout.positions.get(id);
      var group = svgElement("g", {
        class: "graph-node",
        transform: "translate(" + position.x + " " + position.y + ")",
        "data-node-id": id,
        "data-section": item.section,
        tabindex: "0",
        role: "button",
        "aria-label": item.label + ": " + item.title
      });

      if (id === state.selectedId) {
        group.classList.add("selected");
      } else if (upstream.has(id)) {
        group.classList.add("upstream");
      } else if (downstream.has(id)) {
        group.classList.add("downstream");
      } else {
        group.classList.add("dim");
      }

      var title = svgElement("title");
      title.textContent = item.label + " - " + item.title;

      var shadow = svgElement("rect", {
        class: "node-shadow",
        x: 2,
        y: 3,
        width: NODE_WIDTH,
        height: NODE_HEIGHT,
        rx: 5
      });
      var halo = svgElement("rect", {
        class: "node-halo",
        x: -4,
        y: -4,
        width: NODE_WIDTH + 8,
        height: NODE_HEIGHT + 8,
        rx: 8
      });
      var box = svgElement("rect", {
        class: "node-box",
        width: NODE_WIDTH,
        height: NODE_HEIGHT,
        rx: 5
      });
      var label = svgElement("text", {
        class: "node-label",
        x: NODE_WIDTH / 2,
        y: 25,
        "text-anchor": "middle"
      });
      label.textContent = item.label;

      group.appendChild(title);
      group.appendChild(shadow);
      group.appendChild(halo);
      group.appendChild(box);
      group.appendChild(label);
      nodeLayer.appendChild(group);
    });

    refs.graphScene.appendChild(edgeLayer);
    refs.graphScene.appendChild(nodeLayer);
    state.graphWidth = layout.width;
    state.graphHeight = layout.height;

    var graphKey = ids.join("|");
    if (graphKey !== state.visibleGraphKey) {
      shouldFit = true;
      state.visibleGraphKey = graphKey;
    }

    refs.graphStats.textContent =
      ids.length + " nodes / " + edgeCount + " direct dependencies";

    if (shouldFit) {
      window.requestAnimationFrame(fitGraph);
    } else {
      applyTransform();
    }
  }

  function escapeDot(value) {
    return String(value)
      .replace(/\\/g, "\\\\")
      .replace(/"/g, '\\"')
      .replace(/\r?\n/g, "\\n");
  }

  function graphModel(ids) {
    var idSet = new Set(ids);
    var edges = [];
    var incoming = new Map();
    var outgoing = new Map();

    ids.forEach(function (id) {
      incoming.set(id, []);
      outgoing.set(id, []);
    });
    ids.forEach(function (targetId) {
      var targetItem = itemById.get(targetId);
      targetItem.dependencies.forEach(function (sourceId) {
        if (!idSet.has(sourceId)) {
          return;
        }
        var edge = {
          source: sourceId,
          target: targetId,
          id: sourceId + "->" + targetId
        };
        edges.push(edge);
        incoming.get(targetId).push(sourceId);
        outgoing.get(sourceId).push(targetId);
      });
    });
    return { ids: ids, edges: edges, incoming: incoming, outgoing: outgoing };
  }

  function graphHighlight(model) {
    var idSet = new Set(model.ids);
    var upstream = ancestorsOf(state.selectedId);
    var downstream = descendantsOf(state.selectedId);
    var upstreamNodes = new Set();
    var downstreamNodes = new Set();
    var upstreamEdges = new Set();
    var downstreamEdges = new Set();

    upstream.forEach(function (id) {
      if (idSet.has(id)) {
        upstreamNodes.add(id);
      }
    });
    downstream.forEach(function (id) {
      if (idSet.has(id)) {
        downstreamNodes.add(id);
      }
    });
    model.edges.forEach(function (edge) {
      if (upstreamNodes.has(edge.source) &&
          (upstreamNodes.has(edge.target) || edge.target === state.selectedId)) {
        upstreamEdges.add(edge.id);
      }
      if ((edge.source === state.selectedId || downstreamNodes.has(edge.source)) &&
          downstreamNodes.has(edge.target)) {
        downstreamEdges.add(edge.id);
      }
    });
    return {
      selected: state.selectedId,
      upstreamNodes: upstreamNodes,
      downstreamNodes: downstreamNodes,
      upstreamEdges: upstreamEdges,
      downstreamEdges: downstreamEdges
    };
  }

  function graphNodeStyle(item, highlight) {
    var palette = {
      deterministic: {
        fill: "#e9effa",
        stroke: "#315fb5",
        font: "#234579"
      },
      stochastic: {
        fill: "#e4f2ed",
        stroke: "#23745d",
        font: "#1c5b49"
      },
      correction: {
        fill: "#f8eae6",
        stroke: "#a14d3d",
        font: "#71372d"
      }
    };
    var base = palette[item.section] || palette.deterministic;
    if (item.id === highlight.selected) {
      return {
        fill: "#f7e8bf",
        stroke: "#a5630f",
        font: "#4b3210",
        width: 2.8
      };
    }
    if (highlight.upstreamNodes.has(item.id)) {
      return {
        fill: "#eee8f8",
        stroke: "#7654a6",
        font: "#4a3970",
        width: 2.2
      };
    }
    if (highlight.downstreamNodes.has(item.id)) {
      return {
        fill: "#fff0d6",
        stroke: "#b97819",
        font: "#744a10",
        width: 2.2
      };
    }
    if (highlight.selected) {
      return {
        fill: "#f7f9fb",
        stroke: "#cbd4dd",
        font: "#8a96a1",
        width: 1.1
      };
    }
    return {
      fill: base.fill,
      stroke: base.stroke,
      font: base.font,
      width: 1.5
    };
  }

  function graphEdgeStyle(edge, highlight) {
    if (highlight.upstreamEdges.has(edge.id) ||
        highlight.downstreamEdges.has(edge.id)) {
      return { color: "#315fc0", width: 2.2 };
    }
    if (highlight.selected) {
      return { color: "#cbd4dd", width: 1.1 };
    }
    return { color: "#aab5bf", width: 1.35 };
  }

  function buildGraphDot(model, highlight) {
    var lines = [
      "digraph G {",
      '  graph [rankdir="LR", bgcolor="transparent", pad="0.25", nodesep="0.28", ranksep="0.72", outputorder="edgesfirst", splines="spline"];',
      '  node [style="rounded,filled", fontname="Segoe UI", fontsize="10", margin="0.15,0.09"];',
      '  edge [arrowhead="normal", arrowsize="0.7"];'
    ];

    model.ids.forEach(function (id) {
      var item = itemById.get(id);
      var style = graphNodeStyle(item, highlight);
      var label = item.label;
      var shape = item.type === "Theorem" || item.type === "Proposition"
        ? "ellipse"
        : "box";
      lines.push(
        '  "' + escapeDot(id) + '" ' +
        '[id="node-' + escapeDot(id) + '" ' +
        'label="' + escapeDot(label) + '" ' +
        'tooltip="' + escapeDot(item.label + " - " + item.title) + '" ' +
        'shape="' + shape + '" ' +
        'fillcolor="' + style.fill + '" ' +
        'color="' + style.stroke + '" ' +
        'fontcolor="' + style.font + '" ' +
        'penwidth="' + style.width + '"];'
      );
    });

    model.edges.slice().sort(function (left, right) {
      return itemSort(left.source, right.source) || itemSort(left.target, right.target);
    }).forEach(function (edge) {
      var style = graphEdgeStyle(edge, highlight);
      lines.push(
        '  "' + escapeDot(edge.source) + '" -> "' + escapeDot(edge.target) + '" ' +
        '[id="edge-' + escapeDot(edge.id) + '" ' +
        'color="' + style.color + '" penwidth="' + style.width + '"];'
      );
    });
    lines.push("}");
    return lines.join("\n");
  }

  function setGraphMessage(message) {
    if (!refs.graphMessage) {
      return;
    }
    refs.graphMessage.textContent = message;
    refs.graphMessage.hidden = !message;
  }

  function loadVizRuntime() {
    if (window.Viz) {
      return Promise.resolve();
    }
    if (!state.vizScriptPromise) {
      state.vizScriptPromise = new Promise(function (resolve, reject) {
        var script = document.createElement("script");
        script.src = "./vendor/viz-global.js";
        script.async = true;
        script.onload = function () { resolve(); };
        script.onerror = function () {
          state.vizScriptPromise = null;
          reject(new Error("Graphviz runtime could not be loaded."));
        };
        document.head.appendChild(script);
      });
    }
    return state.vizScriptPromise;
  }

  function getGraphviz() {
    if (state.graphviz) {
      return Promise.resolve(state.graphviz);
    }
    if (!state.graphvizPromise) {
      state.graphvizPromise = loadVizRuntime()
        .then(function () { return window.Viz.instance(); })
        .then(function (viz) {
          state.graphviz = viz;
          return viz;
        })
        .catch(function (error) {
          state.graphvizPromise = null;
          throw error;
        });
    }
    return state.graphvizPromise;
  }

  function graphSvgSize(svg) {
    var viewBox = svg.getAttribute("viewBox");
    if (viewBox) {
      var values = viewBox.trim().split(/[ ,]+/).map(Number);
      if (values.length === 4 && values.every(function (value) {
        return Number.isFinite(value);
      })) {
        return { width: values[2], height: values[3] };
      }
    }
    return {
      width: parseFloat(svg.getAttribute("width")) || 800,
      height: parseFloat(svg.getAttribute("height")) || 500
    };
  }

  function decorateGraphSvg(svg, model, highlight) {
    var nodesById = new Map();
    model.ids.forEach(function (id) { nodesById.set(id, itemById.get(id)); });

    svg.querySelectorAll("g.node").forEach(function (node) {
      var title = node.querySelector("title");
      var id = title ? title.textContent.trim() : "";
      if (!nodesById.has(id)) {
        var rawId = node.getAttribute("id") || "";
        id = rawId.replace(/^node-/, "");
      }
      var item = nodesById.get(id);
      if (!item) {
        return;
      }
      node.setAttribute("data-node-id", id);
      node.setAttribute("data-section", item.section);
      node.setAttribute("tabindex", "0");
      node.setAttribute("role", "button");
      node.setAttribute("aria-label", item.label + ": " + item.title);
      node.classList.add("graph-node");
      if (id === highlight.selected) {
        node.classList.add("selected");
      } else if (highlight.upstreamNodes.has(id)) {
        node.classList.add("upstream");
      } else if (highlight.downstreamNodes.has(id)) {
        node.classList.add("downstream");
      } else {
        node.classList.add("dim");
      }
    });

    svg.querySelectorAll("g.edge").forEach(function (edgeGroup) {
      var title = edgeGroup.querySelector("title");
      var edgeId = title ? title.textContent.trim() : "";
      edgeGroup.classList.add("graph-edge");
      if (highlight.upstreamEdges.has(edgeId)) {
        edgeGroup.classList.add("upstream");
      } else if (highlight.downstreamEdges.has(edgeId)) {
        edgeGroup.classList.add("downstream");
      } else if (highlight.selected) {
        edgeGroup.classList.add("dim");
      }
    });
  }

  function renderGraph(options) {
    var ids = graphVisibleIds();
    var shouldFit = Boolean(options && options.fit);
    var graphKey = ids.join("|");
    var graphChanged = graphKey !== state.visibleGraphKey;
    var preserveView = Boolean(
      options && (options.preserveView === true || options.fit === false)
    );
    var model = graphModel(ids);
    var highlight = graphHighlight(model);
    var token = ++state.renderToken;

    refs.graphEmpty.hidden = ids.length > 0;
    if (!ids.length) {
      refs.graphScene.replaceChildren();
      refs.graphStats.textContent = "No graph items";
      setGraphMessage("");
      return;
    }

    refs.graphStats.innerHTML =
      '<span class="stat-pill">article deps</span>' +
      '<span class="stat-pill">' + ids.length + ' nodes</span>' +
      '<span class="stat-pill">' + model.edges.length + ' edges</span>' +
      '<span class="stat-pill">' + (state.graphMode === "focus" ? "neighborhood" : "full graph") + '</span>';
    setGraphMessage("Rendering Graphviz layout.");

    getGraphviz()
      .then(function (viz) {
        if (token !== state.renderToken) {
          return;
        }
        var svgText = viz.renderString(buildGraphDot(model, highlight), {
          format: "svg",
          engine: "dot"
        });
        var parsed = new DOMParser().parseFromString(svgText, "image/svg+xml");
        var svg = parsed.documentElement;
        var size = graphSvgSize(svg);
        // Keep the Graphviz coordinate system explicit so the outer scene can
        // apply the same pan/zoom transform as the reference graph viewer.
        svg.setAttribute("width", String(size.width));
        svg.setAttribute("height", String(size.height));
        svg.setAttribute("role", "img");
        svg.setAttribute("aria-label", "Article dependency graph");
        svg.setAttribute("preserveAspectRatio", "xMinYMin meet");
        decorateGraphSvg(svg, model, highlight);
        refs.graphScene.replaceChildren(svg);
        state.graphWidth = size.width;
        state.graphHeight = size.height;
        state.graphBaseWidth = size.width;
        state.graphBaseHeight = size.height;
        state.visibleGraphKey = graphKey;
        if (shouldFit || graphChanged || !preserveView) {
          window.requestAnimationFrame(fitGraph);
        } else {
          applyTransform();
        }
        setGraphMessage("");
      })
      .catch(function () {
        if (token !== state.renderToken) {
          return;
        }
        setGraphMessage("Graphviz unavailable; showing the built-in layout.");
        renderGraphFallback({ fit: shouldFit || graphChanged });
      });
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
      1.4
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
    var newScale = Math.max(
      MIN_ZOOM,
      Math.min(MAX_ZOOM, oldScale * factor)
    );

    state.transform.x =
      pointX - (pointX - state.transform.x) * (newScale / oldScale);
    state.transform.y =
      pointY - (pointY - state.transform.y) * (newScale / oldScale);
    state.transform.scale = newScale;
    applyTransform();
  }

  function renderHeader() {
    var item = selectedItem();
    refs.currentLabel.textContent = item.label;
    refs.currentTitle.textContent = item.title;
    refs.fullGraphButton.classList.toggle("active", state.graphMode === "full");
    refs.focusGraphButton.classList.toggle("active", state.graphMode === "focus");
  }

  function relationLink(item) {
    var button = document.createElement("button");
    button.type = "button";
    button.className = "relation-link";
    button.dataset.selectItem = item.id;

    var dot = document.createElement("span");
    dot.className = "relation-dot " + item.section;

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

    if (ids.length === 0) {
      var empty = document.createElement("div");
      empty.className = "relation-empty";
      empty.textContent = "None at article level.";
      list.appendChild(empty);
    } else {
      ids
        .slice()
        .sort(itemSort)
        .forEach(function (id) {
          list.appendChild(relationLink(itemById.get(id)));
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
    var consumers = consumersById.get(item.id) || [];
    var header = document.createElement("header");
    header.className = "detail-header";

    var kicker = document.createElement("div");
    kicker.className = "detail-kicker";
    var kind = document.createElement("span");
    kind.className = "detail-kind";
    kind.textContent = item.type;
    var sectionTag = document.createElement("span");
    sectionTag.className = "detail-section-tag " + item.section;
    sectionTag.textContent = SECTION_META[item.section].short;
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
    var sourceText = document.createElement("span");
    sourceText.textContent = "Open source at line " + item.line;
    source.appendChild(leanMark);
    source.appendChild(sourceText);

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
    var template = document.getElementById("statement-" + item.id);
    if (template) {
      statement.appendChild(template.content.cloneNode(true));
    }
    statementSection.appendChild(statementHeading);
    statementSection.appendChild(statement);

    var relationSection = document.createElement("section");
    relationSection.className = "detail-section";
    var relationHeading = document.createElement("h3");
    relationHeading.textContent = "Article-level relations";
    var relationGrid = document.createElement("div");
    relationGrid.className = "relation-grid";
    relationGrid.appendChild(
      relationColumn("Direct dependencies", item.dependencies)
    );
    relationGrid.appendChild(
      relationColumn("Used directly by", consumers)
    );
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
    factRow(facts, "Version", LEAN_REF);
    factRow(facts, "Lean snapshot", LEAN_COMMIT.slice(0, 8));
    leanSection.appendChild(leanHeading);
    leanSection.appendChild(facts);

    refs.detailContent.replaceChildren(
      header,
      statementSection,
      relationSection,
      leanSection
    );
    refs.detailContent.parentElement.scrollTop = 0;
    queueMathTypeset();
  }

  function queueMathTypeset() {
    state.mathQueue = state.mathQueue
      .then(function () {
        if (!window.MathJax || !window.MathJax.typesetPromise) {
          return null;
        }
        if (window.MathJax.typesetClear) {
          window.MathJax.typesetClear([refs.detailContent]);
        }
        return window.MathJax.typesetPromise([refs.detailContent]);
      })
      .catch(function () {
        return null;
      });
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

  function selectItem(id, options) {
    if (!itemById.has(id)) {
      return;
    }
    state.selectedId = id;
    if (!options || options.updateHash !== false) {
      window.history.replaceState(null, "", "#" + id);
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
    writePreference("tr-lalm-map:graph-mode", state.graphMode);
    renderHeader();
    renderGraph({ fit: true });
  }

  function setSidebarCollapsed(collapsed) {
    state.sidebarCollapsed = Boolean(collapsed);
    refs.appShell.classList.toggle("sidebar-collapsed", state.sidebarCollapsed);
    refs.sidebarToggle.textContent = state.sidebarCollapsed ? ">" : "<";
    refs.sidebarToggle.setAttribute(
      "aria-expanded",
      String(!state.sidebarCollapsed)
    );
    refs.sidebarToggle.setAttribute(
      "aria-label",
      state.sidebarCollapsed ? "Expand index" : "Collapse index"
    );
    refs.sidebarToggle.title =
      state.sidebarCollapsed ? "Expand index" : "Collapse index";
    writePreference(
      "tr-lalm-map:sidebar-collapsed",
      String(state.sidebarCollapsed)
    );
    window.setTimeout(fitGraph, 170);
  }

  function setDetailCollapsed(collapsed) {
    state.detailCollapsed = Boolean(collapsed);
    refs.appShell.classList.toggle("detail-collapsed", state.detailCollapsed);
    refs.detailToggle.textContent = state.detailCollapsed ? "<" : ">";
    refs.detailToggle.setAttribute(
      "aria-expanded",
      String(!state.detailCollapsed)
    );
    refs.detailToggle.setAttribute(
      "aria-label",
      state.detailCollapsed ? "Expand statement" : "Collapse statement"
    );
    refs.detailToggle.title =
      state.detailCollapsed ? "Expand statement" : "Collapse statement";
    writePreference(
      "tr-lalm-map:detail-collapsed",
      String(state.detailCollapsed)
    );
    window.setTimeout(fitGraph, 170);
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
      if (state.visibleListIds.length === 0) {
        return;
      }
      var index = state.visibleListIds.indexOf(state.selectedId);
      var direction = event.key === "ArrowDown" ? 1 : -1;
      if (index < 0) {
        index = direction > 0 ? -1 : 0;
      }
      var nextIndex =
        (index + direction + state.visibleListIds.length) %
        state.visibleListIds.length;
      selectItem(state.visibleListIds[nextIndex], { updateHash: true });
      var active = refs.itemList.querySelector(".item-row.active");
      if (active) {
        active.scrollIntoView({ block: "nearest" });
      }
    });

    refs.fullGraphButton.addEventListener("click", function () {
      setGraphMode("full");
    });
    refs.focusGraphButton.addEventListener("click", function () {
      setGraphMode("focus");
    });
    refs.zoomOutButton.addEventListener("click", function () {
      zoomAt(0.82);
    });
    refs.zoomInButton.addEventListener("click", function () {
      zoomAt(1.22);
    });
    refs.fitButton.addEventListener("click", fitGraph);

    refs.mobileGraphButton.addEventListener("click", function () {
      setMobileView("graph");
    });
    refs.mobileDetailButton.addEventListener("click", function () {
      setMobileView("detail");
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
        return;
      }
      var reference = event.target.closest("[data-item-ref]");
      if (reference) {
        event.preventDefault();
        selectItem(reference.dataset.itemRef, { mobileDetail: true });
      }
    });

    refs.graphViewport.addEventListener("wheel", function (event) {
      event.preventDefault();
      zoomAt(Math.exp(-event.deltaY * 0.0012), event.clientX, event.clientY);
    }, { passive: false });

    refs.graphViewport.addEventListener("pointerdown", function (event) {
      var target = event.target instanceof Element ? event.target : null;
      var node = target ? target.closest("[data-node-id]") : null;
      event.preventDefault();
      refs.graphViewport.setPointerCapture(event.pointerId);
      refs.graphViewport.classList.add("dragging");
      state.pointer = {
        id: event.pointerId,
        nodeId: node ? node.dataset.nodeId : "",
        startX: event.clientX,
        startY: event.clientY,
        originX: state.transform.x,
        originY: state.transform.y,
        moved: false
      };
    });

    refs.graphViewport.addEventListener("pointermove", function (event) {
      if (!state.pointer || state.pointer.id !== event.pointerId) {
        return;
      }
      var deltaX = event.clientX - state.pointer.startX;
      var deltaY = event.clientY - state.pointer.startY;
      if (Math.abs(deltaX) + Math.abs(deltaY) > 4) {
        state.pointer.moved = true;
      }
      state.transform.x =
        state.pointer.originX + deltaX;
      state.transform.y =
        state.pointer.originY + deltaY;
      applyTransform();
    });

    function endPointer(event) {
      if (!state.pointer || state.pointer.id !== event.pointerId) {
        return;
      }
      var tappedNodeId = state.pointer.moved ? "" : state.pointer.nodeId;
      state.pointer = null;
      refs.graphViewport.classList.remove("dragging");
      if (refs.graphViewport.hasPointerCapture(event.pointerId)) {
        refs.graphViewport.releasePointerCapture(event.pointerId);
      }
      if (tappedNodeId) {
        selectItem(tappedNodeId, { mobileDetail: false });
      }
    }

    refs.graphViewport.addEventListener("pointerup", endPointer);
    refs.graphViewport.addEventListener("pointercancel", endPointer);
    refs.graphViewport.addEventListener("dblclick", fitGraph);

    document.addEventListener("keydown", function (event) {
      var target = event.target;
      var isTyping =
        target instanceof HTMLInputElement ||
        target instanceof HTMLSelectElement ||
        target instanceof HTMLTextAreaElement;
      if (event.key === "/" && !isTyping) {
        event.preventDefault();
        refs.searchInput.focus();
      } else if (event.key === "Escape" && target === refs.searchInput) {
        refs.searchInput.value = "";
        renderList();
        refs.searchInput.blur();
      }
    });

    window.addEventListener("hashchange", function () {
      var id = window.location.hash.replace(/^#/, "");
      if (itemById.has(id) && id !== state.selectedId) {
        selectItem(id, { updateHash: false });
      }
    });

    var resizeTimer = null;
    window.addEventListener("resize", function () {
      window.clearTimeout(resizeTimer);
      resizeTimer = window.setTimeout(fitGraph, 100);
    });
    window.addEventListener("load", queueMathTypeset);
  }

  function validateData() {
    var errors = [];
    var edgeCount = 0;

    ITEMS.forEach(function (item) {
      if (!document.getElementById("statement-" + item.id)) {
        errors.push("Missing statement template: " + item.id);
      }
      item.dependencies.forEach(function (dependencyId) {
        edgeCount += 1;
        if (!itemById.has(dependencyId)) {
          errors.push(item.id + " has unknown dependency " + dependencyId);
        }
      });
    });

    if (ITEMS.length !== 24) {
      errors.push("Expected 24 article items, found " + ITEMS.length);
    }
    if (edgeCount !== 42) {
      errors.push("Expected 42 direct dependencies, found " + edgeCount);
    }
    if (errors.length > 0) {
      throw new Error(errors.join("\n"));
    }
  }

  function initialize() {
    validateData();
    populateTypeFilter();
    setSidebarCollapsed(state.sidebarCollapsed);
    setDetailCollapsed(state.detailCollapsed);
    setMobileView(state.mobileView);
    bindEvents();
    renderHeader();
    renderList();
    renderDetail();
    renderGraph({ fit: true });
  }

  initialize();
}());
