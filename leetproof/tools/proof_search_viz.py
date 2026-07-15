"""Interactive visualization for MCTS proof search trees.

Serializes the search tree and step-by-step trace, saves JSON, and
renders a self-contained HTML file with D3.js interactive visualization.

Workflow:
  1. Search with ``trace=True`` → saves ``.json`` alongside results
  2. Render JSON → HTML via ``render_json_to_html()`` or the CLI::

       uv run python tools/proof_search_viz.py output/viz/map_map_length.json

Or all-in-one via the test script::

    uv run python scripts/test_proof_search_cases.py --case fib --visualize
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from pantograph.search import SearchState


# ---------------------------------------------------------------------------
# Trace data structures
# ---------------------------------------------------------------------------

@dataclass
class SearchTrace:
    """Accumulates MCTS search events for later visualization."""

    steps: list[dict] = field(default_factory=list)
    metadata: dict = field(default_factory=dict)
    # Internal: maps Python object id → stable integer node id
    _id_map: dict[int, int] = field(default_factory=dict, repr=False)
    _next_id: int = field(default=0, repr=False)

    def assign_id(self, node: SearchState) -> int:
        """Get or create a stable integer ID for a SearchState node."""
        obj_id = id(node)
        if obj_id not in self._id_map:
            self._id_map[obj_id] = self._next_id
            self._next_id += 1
        return self._id_map[obj_id]

    def record_step(
        self,
        step: int,
        trajectory: list[SearchState],
        tactic: str | None,
        result: str,
        child: SearchState | None = None,
        *,
        child_value: float | None = None,
        child_goal_count: int | None = None,
        child_solved: bool | None = None,
    ) -> None:
        """Record a single MCTS iteration."""
        rec: dict[str, Any] = {
            "step": step,
            "trajectory": [self.assign_id(n) for n in trajectory],
            "selected": self.assign_id(trajectory[-1]),
            "tactic": tactic,
            "result": result,  # "success", "failure", "exhausted", "solved", "error"
        }
        if child is not None:
            rec["child_id"] = self.assign_id(child)
            if child_value is None:
                child_value = float(getattr(child, "total_value", 0.0) or 0.0)
            rec["child_value"] = round(child_value, 4)

            if child_goal_count is None:
                child_goal_count = len(child.goal_state.goals) if child.goal_state else 0
            rec["child_goal_count"] = child_goal_count

            if child_solved is None:
                child_solved = bool(child.goal_state.is_solved) if child.goal_state else False
            rec["child_solved"] = child_solved
        self.steps.append(rec)


# ---------------------------------------------------------------------------
# Tree serialization
# ---------------------------------------------------------------------------

def _serialize_goal(goal) -> dict:
    """Serialize a single Pantograph Goal to a dict."""
    variables = []
    for v in (goal.variables or []):
        variables.append({
            "name": v.name or "",
            "type": str(v.t) if v.t else "",
            "value": str(v.v) if hasattr(v, "v") and v.v else None,
        })
    return {
        "target": str(goal.target) if goal.target else "",
        "variables": variables,
    }


def serialize_tree(
    root: SearchState,
    trace: SearchTrace | None = None,
    node_data: Callable[[SearchState], dict[str, Any]] | None = None,
) -> dict:
    """Recursively serialize the MCTS tree to a JSON-friendly dict.

    Assigns clean sequential IDs in DFS order (0, 1, 2, ...).
    If a trace is provided, builds a mapping from the trace's internal IDs
    to these new DFS-order IDs so that trace steps can be remapped.

    Includes full proof state information (goals + hypotheses) at each node.
    """
    counter = [0]
    # old trace ID → new DFS-order ID
    id_remap: dict[int, int] = {}

    def _serialize(node: SearchState) -> dict:
        new_id = counter[0]
        counter[0] += 1

        # Build remap from trace's internal ID to the new sequential ID
        if trace is not None:
            obj_id = id(node)
            if obj_id in trace._id_map:
                old_id = trace._id_map[obj_id]
                id_remap[old_id] = new_id

        goals = node.goal_state.goals if node.goal_state else []
        serialized_goals = [_serialize_goal(g) for g in goals]

        total_value = float(getattr(node, "total_value", 0.0) or 0.0)
        result: dict[str, Any] = {
            "id": new_id,
            "tactic": getattr(node, "tactic_applied", None),
            "goals": serialized_goals,
            "goal_count": len(goals),
            "is_solved": node.goal_state.is_solved if node.goal_state else False,
            "total_value": round(total_value, 4),
            "visit_count": int(getattr(node, "visit_count", 0) or 0),
            "avg_value": 0.0,
            "exhausted": getattr(node, "exhausted", False),
            "subtree_exhausted": getattr(node, "subtree_exhausted", False),
            "tested_tactics": [str(t) for t in (getattr(node, "tested_tactics", []) or [])],
            "children": [],
        }

        if node_data is not None:
            result.update(node_data(node))

        visit_count = max(int(result.get("visit_count", 0) or 0), 1)
        result["avg_value"] = round(float(result.get("total_value", 0.0) or 0.0) / visit_count, 4)

        for child in node.children or []:
            result["children"].append(_serialize(child))

        return result

    tree = _serialize(root)

    # Remap trace step IDs to the new DFS-order IDs
    if trace is not None:
        for step in trace.steps:
            step["trajectory"] = [id_remap.get(x, x) for x in step.get("trajectory", [])]
            step["selected"] = id_remap.get(step.get("selected", -1), step.get("selected", -1))
            if "child_id" in step:
                step["child_id"] = id_remap.get(step["child_id"], step["child_id"])

    return tree


# ---------------------------------------------------------------------------
# Proof-path extraction
# ---------------------------------------------------------------------------

def _find_proof_path(node: dict, path: list[int] | None = None) -> list[int] | None:
    """DFS to find the path from root to a solved leaf. Returns node IDs."""
    if path is None:
        path = []
    path = path + [node["id"]]
    if node["is_solved"]:
        return path
    for child in node.get("children", []):
        result = _find_proof_path(child, path)
        if result is not None:
            return result
    return None


# ---------------------------------------------------------------------------
# HTML generation
# ---------------------------------------------------------------------------

_HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>MCTS Proof Search — __TITLE__</title>
<script src="https://d3js.org/d3.v7.min.js"></script>
<style>
* { margin: 0; padding: 0; box-sizing: border-box; }
body { font-family: 'Menlo', 'Consolas', 'Monaco', monospace; background: #1a1a2e; color: #e0e0e0; overflow: hidden; height: 100vh; }

/* Header */
#header { background: #16213e; padding: 10px 20px; display: flex; align-items: center; gap: 20px; border-bottom: 1px solid #0f3460; height: 50px; }
#header h1 { font-size: 14px; color: #e94560; white-space: nowrap; }
.badge { display: inline-block; padding: 2px 8px; border-radius: 4px; font-size: 11px; font-weight: bold; }
.badge-success { background: #1b5e20; color: #a5d6a7; }
.badge-fail { background: #b71c1c; color: #ef9a9a; }
.stat { font-size: 11px; color: #8899aa; }

/* Main layout */
#main { display: flex; height: calc(100vh - 50px - 60px); }
#tree-container { flex: 1; overflow: hidden; cursor: grab; }
#tree-container:active { cursor: grabbing; }
#detail-panel { width: 360px; background: #16213e; border-left: 1px solid #0f3460; overflow-y: auto; padding: 12px; font-size: 12px; }

/* Detail panel */
.detail-section { margin-bottom: 12px; }
.detail-section h3 { color: #e94560; font-size: 11px; text-transform: uppercase; letter-spacing: 1px; margin-bottom: 6px; padding-bottom: 4px; border-bottom: 1px solid #0f3460; }
.detail-row { display: flex; justify-content: space-between; margin-bottom: 3px; }
.detail-label { color: #8899aa; }
.detail-value { color: #e0e0e0; text-align: right; max-width: 200px; word-break: break-all; }
.goal-block { background: #0a0a1a; border: 1px solid #0f3460; border-radius: 4px; padding: 8px; margin-bottom: 6px; font-size: 11px; white-space: pre-wrap; overflow-x: auto; }
.goal-target { color: #64ffda; }
.goal-var { color: #90caf9; }
.tactic-tag { display: inline-block; background: #0f3460; color: #90caf9; padding: 1px 6px; border-radius: 3px; margin: 1px; font-size: 10px; }
.tactic-tag.applied { background: #1b5e20; color: #a5d6a7; }

/* Replay bar */
#replay-bar { background: #16213e; border-top: 1px solid #0f3460; padding: 8px 20px; display: flex; align-items: center; gap: 12px; height: 60px; }
#replay-bar label { font-size: 11px; color: #8899aa; white-space: nowrap; }
#step-slider { flex: 1; accent-color: #e94560; }
#step-info { font-size: 11px; color: #e0e0e0; min-width: 300px; }
.btn { background: #0f3460; color: #e0e0e0; border: 1px solid #1a1a4e; padding: 4px 12px; border-radius: 4px; cursor: pointer; font-size: 11px; font-family: inherit; }
.btn:hover { background: #1a1a5e; }
.btn.active { background: #e94560; }

/* SVG styles */
.link path { fill: none; stroke: #334; stroke-width: 1.5px; }
.link.proof-path path { stroke: #4CAF50; stroke-width: 3px; }
.link.highlighted path { stroke: #FFD700; stroke-width: 2.5px; }
.link text { fill: #8899aa; font-size: 9px; pointer-events: none; }
.link.proof-path text { fill: #a5d6a7; font-weight: bold; }
.link.highlighted text { fill: #FFD700; }
.node circle { stroke: #222; stroke-width: 1.5px; cursor: pointer; transition: r 0.2s; }
.node circle:hover { stroke: #fff; stroke-width: 2px; }
.node.selected circle { stroke: #FFD700; stroke-width: 3px; }
.node text { font-size: 9px; fill: #aaa; pointer-events: none; }
.node.proof-path circle { stroke: #4CAF50; stroke-width: 3px; }
.node.highlighted circle { stroke: #FFD700; stroke-width: 2.5px; }

/* Legend */
#legend { position: absolute; bottom: 70px; left: 10px; background: rgba(22,33,62,0.9); border: 1px solid #0f3460; border-radius: 4px; padding: 8px; font-size: 10px; }
#legend .item { display: flex; align-items: center; gap: 6px; margin-bottom: 3px; }
#legend .swatch { width: 12px; height: 12px; border-radius: 50%; border: 1px solid #333; }
</style>
</head>
<body>

<div id="header">
  <h1>__TITLE__</h1>
  <span class="badge __STATUS_CLASS__">__STATUS_TEXT__</span>
  <span class="stat">Steps: __STEPS__</span>
  <span class="stat">Duration: __DURATION__s</span>
  <span class="stat">Nodes: <span id="node-count"></span></span>
  <span class="stat">Max depth: <span id="max-depth"></span></span>
</div>

<div id="main">
  <div id="tree-container"></div>
  <div id="detail-panel">
    <div class="detail-section">
      <h3>Node Details</h3>
      <p style="color: #556; font-size: 11px;">Click a node to inspect</p>
    </div>
  </div>
</div>

<div id="replay-bar">
  <button class="btn" id="btn-proof" title="Highlight proof path">Proof Path</button>
  <button class="btn" id="btn-play" title="Play/pause replay">Play</button>
  <button class="btn" id="btn-reset" title="Reset highlights">Reset</button>
  <label>Step:</label>
  <input type="range" id="step-slider" min="0" max="0" value="0">
  <div id="step-info">Move slider to replay search</div>
</div>

<div id="legend">
  <div class="item"><div class="swatch" style="background:#4CAF50"></div> Solved</div>
  <div class="item"><div class="swatch" style="background:#f44336"></div> Exhausted</div>
  <div class="item"><div class="swatch" style="background:#2196F3"></div> Expanded</div>
  <div class="item"><div class="swatch" style="background:#78909C"></div> Leaf</div>
  <div class="item"><div class="swatch" style="background:#FFD700"></div> Proof path / replay</div>
</div>

<script>
// --- Embedded data ---
const TREE_DATA = __TREE_JSON__;
const TRACE_STEPS = __TRACE_JSON__;
const PROOF_PATH = __PROOF_PATH_JSON__;

// --- Helpers ---
function countNodes(node) {
  let c = 1;
  (node.children || []).forEach(ch => c += countNodes(ch));
  return c;
}
function maxDepth(node, d) {
  d = d || 0;
  let m = d;
  (node.children || []).forEach(ch => { m = Math.max(m, maxDepth(ch, d + 1)); });
  return m;
}
function nodeColor(d) {
  if (d.data.is_solved) return "#4CAF50";
  if (d.data.subtree_exhausted || d.data.exhausted) return "#f44336";
  if ((d.data.children || []).length > 0) return "#2196F3";
  return "#78909C";
}
function nodeRadius(d) {
  return Math.max(4, Math.min(14, Math.log(d.data.visit_count + 1) * 3));
}

// --- Stats ---
document.getElementById("node-count").textContent = countNodes(TREE_DATA);
document.getElementById("max-depth").textContent = maxDepth(TREE_DATA);

// --- Build node id lookup ---
const nodeById = {};
function indexNodes(node) {
  nodeById[node.id] = node;
  (node.children || []).forEach(indexNodes);
}
indexNodes(TREE_DATA);

// --- D3 Tree ---
const container = document.getElementById("tree-container");
const width = container.clientWidth;
const height = container.clientHeight;

const svg = d3.select("#tree-container")
  .append("svg")
  .attr("width", width)
  .attr("height", height);

const g = svg.append("g");

// Zoom
const zoom = d3.zoom()
  .scaleExtent([0.05, 4])
  .on("zoom", (event) => g.attr("transform", event.transform));
svg.call(zoom);

// Build hierarchy
const root = d3.hierarchy(TREE_DATA);

// Collapsible: store all children for toggle support, but start fully expanded
root.descendants().forEach(d => {
  d._allChildren = d.children;
});

// Tree layout
const treeLayout = d3.tree().nodeSize([22, 180]);

let linkGroup = g.append("g").attr("class", "links");
let nodeGroup = g.append("g").attr("class", "nodes");
let selectedNode = null;

function update(source) {
  treeLayout(root);

  // Normalize for fixed-depth
  root.descendants().forEach(d => { d.y = d.depth * 200; });

  const duration = 300;

  // Links
  const links = linkGroup.selectAll("g.link")
    .data(root.links(), d => d.target.data.id);

  const linkEnter = links.enter()
    .append("g")
    .attr("class", "link");

  linkEnter.append("path");
  linkEnter.append("text");

  const linkMerge = linkEnter.merge(links);

  linkMerge.select("path")
    .transition().duration(duration)
    .attr("d", d3.linkHorizontal().x(d => d.y).y(d => d.x));

  linkMerge.select("text")
    .transition().duration(duration)
    .attr("x", d => (d.source.y + d.target.y) / 2)
    .attr("y", d => (d.source.x + d.target.x) / 2 - 4)
    .attr("text-anchor", "middle")
    .text(d => {
      const t = d.target.data.tactic || "";
      return t.length > 28 ? t.slice(0, 25) + "..." : t;
    });

  // Mark proof-path links
  const ppSet = new Set(PROOF_PATH);
  linkMerge.classed("proof-path", d =>
    ppSet.has(d.source.data.id) && ppSet.has(d.target.data.id) && document.getElementById("btn-proof").classList.contains("active")
  );

  links.exit().remove();

  // Nodes
  const nodes = nodeGroup.selectAll("g.node")
    .data(root.descendants(), d => d.data.id);

  const nodeEnter = nodes.enter()
    .append("g")
    .attr("class", "node")
    .attr("transform", d => `translate(${d.y},${d.x})`);

  nodeEnter.append("circle");
  nodeEnter.append("text")
    .attr("dy", -10)
    .attr("text-anchor", "middle");

  const nodeMerge = nodeEnter.merge(nodes);

  nodeMerge
    .transition().duration(duration)
    .attr("transform", d => `translate(${d.y},${d.x})`);

  nodeMerge.select("circle")
    .attr("r", nodeRadius)
    .attr("fill", nodeColor)
    .on("click", (event, d) => {
      event.stopPropagation();
      if (event.shiftKey || event.metaKey) {
        // Toggle collapse
        if (d.children) {
          d._children = d.children;
          d.children = null;
        } else if (d._children) {
          d.children = d._children;
          d._children = null;
        }
        update(d);
      } else {
        showDetails(d);
      }
    })
    .on("dblclick", (event, d) => {
      event.stopPropagation();
      if (d.children) {
        d._children = d.children;
        d.children = null;
      } else if (d._children) {
        d.children = d._children;
        d._children = null;
      }
      update(d);
    });

  // Label: node ID (checkmark for solved)
  nodeMerge.select("text")
    .text(d => {
      if (d.data.is_solved) return "\u2713";
      return d.data.id;
    });

  // Proof-path class
  nodeMerge.classed("proof-path", d =>
    ppSet.has(d.data.id) && document.getElementById("btn-proof").classList.contains("active")
  );

  nodeMerge.classed("selected", d => selectedNode && d.data.id === selectedNode.data.id);

  nodes.exit().remove();
}

update(root);

// Center view on root
svg.call(zoom.transform, d3.zoomIdentity
  .translate(60, height / 2)
  .scale(0.9));

// --- Detail panel ---
function showDetails(d) {
  selectedNode = d;
  const data = d.data;
  const panel = document.getElementById("detail-panel");

  let html = '';

  // Header
  html += '<div class="detail-section"><h3>Node #' + data.id + '</h3>';
  html += '<div class="detail-row"><span class="detail-label">Status</span><span class="detail-value">';
  if (data.is_solved) html += '<span style="color:#4CAF50">SOLVED</span>';
  else if (data.subtree_exhausted) html += '<span style="color:#f44336">SUBTREE EXHAUSTED</span>';
  else if (data.exhausted) html += '<span style="color:#f44336">EXHAUSTED</span>';
  else html += '<span style="color:#2196F3">ACTIVE</span>';
  html += '</span></div>';
  html += '<div class="detail-row"><span class="detail-label">Depth</span><span class="detail-value">' + d.depth + '</span></div>';
  html += '</div>';

  // Tactic
  if (data.tactic) {
    html += '<div class="detail-section"><h3>Tactic Applied</h3>';
    html += '<div class="goal-block" style="color:#FFD700">' + escHtml(data.tactic) + '</div>';
    html += '</div>';
  }

  // MCTS stats
  html += '<div class="detail-section"><h3>MCTS Statistics</h3>';
  html += '<div class="detail-row"><span class="detail-label">Visits</span><span class="detail-value">' + data.visit_count + '</span></div>';
  html += '<div class="detail-row"><span class="detail-label">Total value</span><span class="detail-value">' + data.total_value + '</span></div>';
  html += '<div class="detail-row"><span class="detail-label">Avg value</span><span class="detail-value">' + data.avg_value + '</span></div>';
  html += '<div class="detail-row"><span class="detail-label">Children</span><span class="detail-value">' + (data.children || []).length + '</span></div>';
  html += '</div>';

  // Proof state — goals
  if (data.goals && data.goals.length > 0) {
    html += '<div class="detail-section"><h3>Proof State (' + data.goals.length + ' goal' + (data.goals.length > 1 ? 's' : '') + ')</h3>';
    data.goals.forEach((goal, i) => {
      html += '<div class="goal-block">';
      // Variables (hypotheses)
      if (goal.variables && goal.variables.length > 0) {
        goal.variables.forEach(v => {
          if (v.name) {
            html += '<span class="goal-var">' + escHtml(v.name) + '</span>';
            if (v.type) html += ' : ' + escHtml(v.type);
            if (v.value) html += ' := ' + escHtml(v.value);
            html += '\n';
          }
        });
        html += '<span style="color:#556">&#x22A2; </span>';
      }
      html += '<span class="goal-target">' + escHtml(goal.target) + '</span>';
      html += '</div>';
    });
    html += '</div>';
  } else if (data.is_solved) {
    html += '<div class="detail-section"><h3>Proof State</h3>';
    html += '<div class="goal-block"><span style="color:#4CAF50">No goals remaining — proof complete!</span></div>';
    html += '</div>';
  }

  // Tested tactics
  if (data.tested_tactics && data.tested_tactics.length > 0) {
    html += '<div class="detail-section"><h3>Tested Tactics (' + data.tested_tactics.length + ')</h3>';
    html += '<div style="line-height: 1.8;">';
    data.tested_tactics.forEach(t => {
      // Check if this tactic produced a child
      const isApplied = (data.children || []).some(ch => ch.tactic === t);
      html += '<span class="tactic-tag' + (isApplied ? ' applied' : '') + '">' + escHtml(t) + '</span> ';
    });
    html += '</div></div>';
  }

  panel.innerHTML = html;
  update(root); // refresh selected state
}

function escHtml(s) {
  const div = document.createElement('div');
  div.textContent = s;
  return div.innerHTML;
}

// --- Replay ---
const slider = document.getElementById("step-slider");
const stepInfo = document.getElementById("step-info");
slider.max = TRACE_STEPS.length > 0 ? TRACE_STEPS.length - 1 : 0;

let playInterval = null;

function clearHighlights() {
  nodeGroup.selectAll("g.node").classed("highlighted", false);
  linkGroup.selectAll("g.link").classed("highlighted", false);
}

function highlightStep(stepIdx) {
  clearHighlights();
  if (stepIdx < 0 || stepIdx >= TRACE_STEPS.length) {
    stepInfo.textContent = "Move slider to replay search";
    return;
  }

  const step = TRACE_STEPS[stepIdx];
  const trajSet = new Set(step.trajectory || []);

  // Expand tree to make trajectory visible
  // (find d3 nodes matching trajectory IDs and ensure they're visible)
  root.descendants().forEach(d => {
    if (trajSet.has(d.data.id)) {
      // Ensure ancestors are expanded
      let ancestor = d.parent;
      while (ancestor) {
        if (!ancestor.children && ancestor._children) {
          ancestor.children = ancestor._children;
          ancestor._children = null;
        }
        ancestor = ancestor.parent;
      }
    }
  });

  update(root);

  // Now highlight after update
  setTimeout(() => {
    nodeGroup.selectAll("g.node")
      .classed("highlighted", d => trajSet.has(d.data.id) || (step.child_id !== undefined && d.data.id === step.child_id));

    linkGroup.selectAll("g.link")
      .classed("highlighted", d => trajSet.has(d.source.data.id) && trajSet.has(d.target.data.id));
  }, 50);

  // Info text
  let info = `Step ${step.step}: `;
  if (step.tactic) info += `"${step.tactic}" → `;
  if (step.result === "success") info += step.child_solved ? "SOLVED!" : `${step.child_goal_count} goal(s)`;
  else if (step.result === "failure") info += "tactic failed";
  else if (step.result === "exhausted") info += "all tactics exhausted";
  else if (step.result === "solved") info += "already solved";
  else if (step.result === "error") info += "error";
  else info += step.result;
  stepInfo.textContent = info;
}

slider.addEventListener("input", () => {
  highlightStep(parseInt(slider.value));
});

document.getElementById("btn-play").addEventListener("click", function() {
  if (playInterval) {
    clearInterval(playInterval);
    playInterval = null;
    this.textContent = "Play";
    this.classList.remove("active");
  } else {
    this.textContent = "Pause";
    this.classList.add("active");
    let idx = parseInt(slider.value);
    playInterval = setInterval(() => {
      if (idx >= TRACE_STEPS.length) {
        clearInterval(playInterval);
        playInterval = null;
        document.getElementById("btn-play").textContent = "Play";
        document.getElementById("btn-play").classList.remove("active");
        return;
      }
      slider.value = idx;
      highlightStep(idx);
      idx++;
    }, 200);
  }
});

document.getElementById("btn-proof").addEventListener("click", function() {
  this.classList.toggle("active");
  clearHighlights();
  update(root);
});

document.getElementById("btn-reset").addEventListener("click", () => {
  clearHighlights();
  slider.value = 0;
  stepInfo.textContent = "Move slider to replay search";
  document.getElementById("btn-proof").classList.remove("active");
  if (playInterval) {
    clearInterval(playInterval);
    playInterval = null;
    document.getElementById("btn-play").textContent = "Play";
    document.getElementById("btn-play").classList.remove("active");
  }
  update(root);
});

// Keyboard shortcuts
document.addEventListener("keydown", (e) => {
  if (e.key === "ArrowRight") {
    slider.value = Math.min(parseInt(slider.value) + 1, TRACE_STEPS.length - 1);
    highlightStep(parseInt(slider.value));
  } else if (e.key === "ArrowLeft") {
    slider.value = Math.max(parseInt(slider.value) - 1, 0);
    highlightStep(parseInt(slider.value));
  } else if (e.key === " ") {
    e.preventDefault();
    document.getElementById("btn-play").click();
  }
});
</script>
</body>
</html>
"""


def generate_visualization(
    trace: SearchTrace,
    tree: dict,
    output_path: str | Path,
    title: str = "Proof Search",
) -> Path:
    """Write a self-contained HTML visualization of the MCTS search tree.

    Args:
        trace: The SearchTrace accumulated during search.
        tree: Serialized tree dict from ``serialize_tree()``.
        output_path: Where to write the HTML file.
        title: Display title (e.g. theorem name).

    Returns:
        The Path to the written file.
    """
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    proof_path = _find_proof_path(tree) or []
    meta = trace.metadata

    html = (_HTML_TEMPLATE
        .replace("__TITLE__", title)
        .replace("__STATUS_CLASS__", "badge-success" if meta.get("success") else "badge-fail")
        .replace("__STATUS_TEXT__", "SOLVED" if meta.get("success") else "FAILED")
        .replace("__STEPS__", str(meta.get("steps", 0)))
        .replace("__DURATION__", f"{meta.get('duration', 0):.2f}")
        .replace("__TREE_JSON__", json.dumps(tree))
        .replace("__TRACE_JSON__", json.dumps(trace.steps))
        .replace("__PROOF_PATH_JSON__", json.dumps(proof_path))
    )

    output_path.write_text(html, encoding="utf-8")

    # Also save raw JSON for programmatic use
    json_path = output_path.with_suffix(".json")
    json_data = {
        "metadata": meta,
        "tree": tree,
        "trace_steps": trace.steps,
        "proof_path": proof_path,
    }
    json_path.write_text(json.dumps(json_data, indent=2), encoding="utf-8")

    return output_path


def render_json_to_html(json_path: str | Path, output_path: str | Path | None = None) -> Path:
    """Render a previously saved JSON trace file into an HTML visualization.

    Args:
        json_path: Path to the ``.json`` file saved by ``generate_visualization``.
        output_path: Where to write the HTML. Defaults to same dir with ``.html`` suffix.

    Returns:
        The Path to the written HTML file.
    """
    json_path = Path(json_path)
    if output_path is None:
        output_path = json_path.with_suffix(".html")
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    data = json.loads(json_path.read_text(encoding="utf-8"))
    meta = data.get("metadata", {})
    tree = data.get("tree", {})
    trace_steps = data.get("trace_steps", [])
    proof_path = data.get("proof_path", [])

    # Derive title from filename if not in metadata
    title = meta.get("title", json_path.stem)

    html = (_HTML_TEMPLATE
        .replace("__TITLE__", title)
        .replace("__STATUS_CLASS__", "badge-success" if meta.get("success") else "badge-fail")
        .replace("__STATUS_TEXT__", "SOLVED" if meta.get("success") else "FAILED")
        .replace("__STEPS__", str(meta.get("steps", 0)))
        .replace("__DURATION__", f"{meta.get('duration', 0):.2f}")
        .replace("__TREE_JSON__", json.dumps(tree))
        .replace("__TRACE_JSON__", json.dumps(trace_steps))
        .replace("__PROOF_PATH_JSON__", json.dumps(proof_path))
    )

    output_path.write_text(html, encoding="utf-8")
    return output_path


# ---------------------------------------------------------------------------
# CLI: render JSON → HTML
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python tools/proof_search_viz.py <trace.json> [output.html]")
        sys.exit(1)

    json_file = sys.argv[1]
    html_file = sys.argv[2] if len(sys.argv) > 2 else None
    out = render_json_to_html(json_file, html_file)
    print(f"Rendered: {out}")
