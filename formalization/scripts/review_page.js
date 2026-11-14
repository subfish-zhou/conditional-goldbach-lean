const D = JSON.parse(document.getElementById("progress-data").textContent),
  $ = (id) => document.getElementById(id),
  rows = D.records,
  byName = new Map(rows.map((r) => [r.name, r]));
let scope = "original",
  status = "all";
const e = (s) =>
  String(s ?? "").replace(
    /[&<>"']/g,
    (c) =>
      ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[
        c
      ],
  );
const theorem = (r) => ["theorem", "lemma"].includes(r.source_kind);
function inScope(r) {
  return scope === "definitions"
    ? !theorem(r)
    : theorem(r) &&
        (scope === "all" || (scope === "original" ? r.original : !r.original));
}
function originalLink(r) {
  return r.review_anchor
    ? `<a href="../outputs/formalization-preparation/review.html#${e(r.review_anchor)}">原文中文 / Lean 审阅条目</a>`
    : "";
}
function markup(r) {
  const refs = r.pending_refs
    .map(
      (n) =>
        `<li><button data-jump="${e(n)}">${e(n.replace("ConditionalGoldbach.", ""))}</button></li>`,
    )
    .join("");
  return `<article class="item" id="${e(r.id)}" data-name="${e(r.name)}"><div class="item-head"><h2>${r.title_html}</h2><span class="badge ${e(r.status)}">${e(r.status_zh)}</span><span class="small">${r.original ? "原审阅声明" : "新增辅助"} · ${e(r.kind_zh)}</span></div><div class="pair"><div class="zh"><p><code>${e(r.short_name)}</code></p>${r.summary_context_note ? `<p class="summary-note">${e(r.summary_context_note)}</p>` : ""}<div class="math-summary">${D.summaries[r.summary_id]}</div><div class="audit-line ${e(r.status)}">${e(r.status_note)}</div>${refs ? `<details open><summary>显式引用链中的待证依赖（${r.pending_refs.length}）</summary><ul class="deps">${refs}</ul></details>` : ""}<details><summary>Lean 传递公理检查</summary><p class="axioms">${r.axioms.length ? r.axioms.map((a) => `<code>${e(a)}</code>`).join(" · ") : "无公理"}</p><p class="small">即使声明本身没有 sorry，只要依赖含 sorryAx，也不会标为证明闭合。依赖列表按显式常量引用追踪；完整传递判定以 Lean.collectAxioms 为准。</p></details>${originalLink(r)}</div><div class="lean"><div class="sourcebar"><span><a href="${e(r.file)}">${e(r.file)}</a> · L${r.line}</span><button data-copy="${e(r.name)}">复制完整声明</button></div><pre tabindex="0" aria-label="${e(r.name)} 的实际 Lean 证明"><code>${highlighted(r)}</code></pre></div></div></article>`;
}
const items = new Map(),
  searchCache = new Map();
function highlighted(r) {
  const lines = [""];
  let start = 0;
  for (const [end, kind] of r.tokens) {
    const text = r.code.slice(start, end),
      cls = D.token_classes[kind];
    start = end;
    text.split("\n").forEach((part, i) => {
      if (i) lines.push("");
      if (part)
        lines[lines.length - 1] += cls
          ? `<span class="tok-${cls}">${e(part)}</span>`
          : e(part);
    });
  }
  return lines
    .map(
      (line, i) =>
        `<span class="code-line" data-line="${r.line + i}">${line}</span>`,
    )
    .join("");
}
function searchable(r) {
  if (!searchCache.has(r.name))
    searchCache.set(
      r.name,
      [
        r.name,
        r.title_zh,
        r.summary_tex,
        r.status_zh,
        r.file,
        r.code,
        ...r.pending_refs,
      ]
        .join(" ")
        .toLowerCase(),
    );
  return searchCache.get(r.name);
}
function filter() {
  const q = $("search").value.trim().toLowerCase();
  let total = 0;
  const selected = rows.filter((r) => {
    const ins = inScope(r);
    if (ins) total++;
    return (
      ins &&
      (status === "all" || r.status === status) &&
      (!q || searchable(r).includes(q))
    );
  });
  const fragment = document.createDocumentFragment(),
    next = new Map();
  for (const r of selected) {
    let node = items.get(r.name);
    if (!node) {
      const t = document.createElement("template");
      t.innerHTML = markup(r);
      node = t.content.firstElementChild;
    }
    next.set(r.name, node);
    fragment.append(node);
  }
  $("list").replaceChildren(fragment);
  items.clear();
  for (const [name, node] of next) items.set(name, node);
  $("count").textContent = `显示 ${selected.length} / ${total} 项`;
  $("empty").hidden = selected.length !== 0;
  document
    .querySelectorAll("[data-scope]")
    .forEach((b) =>
      b.setAttribute("aria-pressed", String(b.dataset.scope === scope)),
    );
  document
    .querySelectorAll("[data-status]")
    .forEach((b) =>
      b.setAttribute("aria-pressed", String(b.dataset.status === status)),
    );
  $("scope-caption").textContent =
    scope === "original"
      ? "当前范围：102 个原审阅定理"
      : scope === "added"
        ? "当前范围：新增辅助定理"
        : scope === "definitions"
          ? "当前范围：定义、缩写与结构"
          : "当前范围：全部公开定理";
}
function jump(name) {
  const r = byName.get(name);
  if (!r) return;
  scope = theorem(r) ? "all" : "definitions";
  status = "all";
  $("search").value = "";
  filter();
  const node = items.get(name);
  node.scrollIntoView({ behavior: "smooth", block: "start" });
  node.classList.add("jump-target");
  setTimeout(() => node.classList.remove("jump-target"), 1800);
  history.replaceState(null, "", "#" + r.id);
}
document.addEventListener("click", async (ev) => {
  const b = ev.target.closest("button");
  if (!b) return;
  if (b.dataset.scope) {
    scope = b.dataset.scope;
    status = "all";
    filter();
  }
  if (b.dataset.status) {
    if (b.classList.contains("stat")) scope = "original";
    status = b.dataset.status;
    filter();
  }
  if (b.dataset.jump) jump(b.dataset.jump);
  if (b.dataset.copy) {
    const text = byName.get(b.dataset.copy).code;
    try {
      if (navigator.clipboard && window.isSecureContext)
        await navigator.clipboard.writeText(text);
      else {
        const area = document.createElement("textarea");
        area.value = text;
        document.body.append(area);
        area.select();
        document.execCommand("copy");
        area.remove();
      }
      $("toast").textContent = "已复制完整 Lean 声明";
      $("toast").hidden = false;
      setTimeout(() => ($("toast").hidden = true), 1600);
    } catch (err) {
      $("toast").textContent = "浏览器阻止复制，请在右栏选择源码";
      $("toast").hidden = false;
    }
  }
});
$("search").addEventListener("input", filter);
$("reset").addEventListener("click", () => {
  scope = "original";
  status = "all";
  $("search").value = "";
  filter();
});
const c = D.metadata.original_theorem_counts;
for (const k of [
  "kernel_closed",
  "proof_written_dependencies_pending",
  "pending_direct_sorry",
])
  $(k + "-count").textContent = c[k];
$("type-note").textContent = D.type_note;
$("meta").textContent = JSON.stringify(D.metadata, null, 2);
$("baseline-count").textContent = rows.filter(
  (r) => theorem(r) && r.original,
).length;
$("added-count").textContent = rows.filter(
  (r) => theorem(r) && !r.original,
).length;
$("all-count").textContent = rows.filter(theorem).length;
$("defs-count").textContent = rows.filter((r) => !theorem(r)).length;
const critical = [
  ...new Set(
    ["theorem_1_1", "theorem_1_2"].flatMap(
      (n) => byName.get("ConditionalGoldbach." + n)?.pending_refs || [],
    ),
  ),
].filter((n) => byName.has(n) && !byName.get(n).kernel_closed);
$("critical-label").textContent = critical.length
  ? "主定理待证依赖："
  : "主定理待证依赖：无";
$("critical").innerHTML = critical
  .map(
    (n) =>
      `<button data-jump="${e(n)}">${e(n.replace("ConditionalGoldbach.", ""))}</button>`,
  )
  .join("");
$("main-status").innerHTML = ["theorem_1_1", "theorem_1_2"]
  .map((n) => byName.get("ConditionalGoldbach." + n))
  .filter(Boolean)
  .map(
    (r) =>
      `<button data-jump="${e(r.name)}">${e(r.short_name)}：${e(r.status_zh)}</button>`,
  )
  .join("");
const mainClosed = ["theorem_1_1", "theorem_1_2"].every(
  (n) => byName.get("ConditionalGoldbach." + n)?.kernel_closed,
);
$("main-warning").textContent =
  c.kernel_closed === 102
    ? "102 条原审阅定理（含附录）的传递依赖均未检出 sorryAx；完整类型及原定义已核对。"
    : mainClosed
      ? "两个主定理的传递依赖均未检出 sorryAx；请同时核对类型同一性记录。"
      : "两个主定理目前尚未端到端完成。已写出的推导仍依赖待证的解析与谱论结果，不能把“证明体完成”视为整篇论文已证明。";
filter();
function restoreFragment() {
  let id;
  try {
    id = decodeURIComponent(location.hash.slice(1));
  } catch {
    return;
  }
  const initial = rows.find((r) => r.id === id);
  if (initial) jump(initial.name);
}
window.addEventListener("hashchange", restoreFragment);
restoreFragment();
