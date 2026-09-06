// Exercise the production status helper, including stale book/item context.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const source = fs.readFileSync(path.join(__dirname, '../docs/app.js'), 'utf8');
const start = source.indexOf('  function evidenceStatuses(');
const end = source.indexOf('\n  function ', start + 1);
assert.ok(start >= 0 && end > start);
const sandbox = vm.createContext({});
vm.runInContext(source.slice(start, end), sandbox);
const statuses = (context, key = 'a') => Object.fromEntries(sandbox.evidenceStatuses(context, key));
const context = {
  item: {key: 'a'}, source: {available: true},
  resources: {docs: {available: true, url: '/docs'}, verso: {available: false, url: ''}, graph: {url: '/graph'}},
  graph: {available: true, selected: 'node', selectedDependencyEvidence: 'compiled', generation: {mode: 'lean-environment-partial'}},
};
for (const value of [context, null, {error: 'offline'}]) {
  assert.deepEqual(Object.keys(statuses(value)), ['Graph', 'Source', 'Docs', 'Verso']);
}
assert.equal(statuses(context).Verso, 'unavailable');
assert.equal(statuses(context).Docs, 'ready');
assert.equal(statuses(context).Graph, 'ready');
assert.equal(statuses(context, 'b').Docs, 'checking');
assert.equal(statuses(null).Docs, 'checking');
assert.equal(statuses({error: 'offline'}).Docs, 'check failed');
assert.equal(statuses({resources: {verso: {available: true}}}).Verso, 'checking');
assert.equal(statuses(context, '').Verso, 'not selected');
context.resources.verso = {available: true, url: '/verso'};
assert.equal(statuses(context).Verso, 'ready');
context.resources.verso.available = false;
assert.equal(statuses(context).Verso, 'unavailable');
context.resources.docs.url = '';
assert.equal(statuses(context).Docs, 'unavailable');
context.source.available = false;
assert.equal(statuses(context).Source, 'unavailable');
context.graph.selectedDependencyEvidence = 'source-only';
assert.equal(statuses(context).Graph, 'source only');
context.graph.selectedDependencyEvidence = 'compiled';
context.graph.generation.mode = 'source-fallback';
assert.equal(statuses(context).Graph, 'source only');
context.graph.generation.mode = 'curated';
assert.equal(statuses(context).Graph, 'unverified');
context.graph.selected = '';
assert.equal(statuses(context).Graph, 'not indexed');
context.graph.available = false;
assert.equal(statuses(context).Graph, 'unavailable');
console.log('Evidence status regressions passed');
