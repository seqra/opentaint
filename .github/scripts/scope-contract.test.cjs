'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');

const engine = require('./scope-contract.cjs');

const EXPECTED_SCOPES = [
  'analyzer',
  'autobuilder',
  'ci',
  'cli',
  'core',
  'docs',
  'github',
  'gitlab',
  'infra',
  'model',
  'rules',
];

test('the contract has one ordered scope declaration', () => {
  assert.deepEqual(engine.contract.scopes, EXPECTED_SCOPES);
  assert.doesNotThrow(() => engine.validateContract(engine.contract));
});

test('scope validation is independent of scope order', () => {
  assert.deepEqual(
    engine.validateScopeList('rules,model,analyzer'),
    ['rules', 'model', 'analyzer'],
  );
  assert.deepEqual(
    engine.validateScopeList('analyzer,model,rules'),
    ['analyzer', 'model', 'rules'],
  );
});

test('scope validation rejects duplicates and unknown scopes', () => {
  assert.throws(() => engine.validateScopeList(''));
  assert.throws(() => engine.validateScopeList('model,model'));
  assert.throws(() => engine.validateScopeList('formal'));
  assert.throws(() => engine.validateScopeList('model,unknown'));
  assert.throws(() => engine.validateScopeList('model,,rules'));
});

test('cli cannot occur with release component scopes', () => {
  for (const forbidden of ['analyzer', 'autobuilder', 'core', 'model', 'rules']) {
    assert.throws(() => engine.validateScopeList(`cli,${forbidden}`));
  }
  assert.doesNotThrow(() => engine.validateScopeList('cli,docs'));
  assert.doesNotThrow(() => engine.validateScopeList('cli,ci'));
});

test('repository integration scopes are mutually exclusive', () => {
  for (const pair of [
    'github,gitlab',
    'github,infra',
    'gitlab,infra',
    'github,gitlab,docs,ci',
  ]) {
    assert.throws(() => engine.validateScopeList(pair));
  }
});

test('repository integration scopes permit docs and ci companions', () => {
  for (const scope of ['github', 'gitlab', 'infra']) {
    assert.doesNotThrow(() => engine.validateScopeList(scope));
    assert.doesNotThrow(() => engine.validateScopeList(`${scope},docs`));
    assert.doesNotThrow(() => engine.validateScopeList(`ci,${scope}`));
    assert.doesNotThrow(() => engine.validateScopeList(`${scope},docs,ci`));
    assert.throws(() => engine.validateScopeList(`${scope},model`));
  }
});

test('all scope subsets agree with the formal compatibility policy', () => {
  const cliForbidden = new Set([
    'analyzer',
    'autobuilder',
    'core',
    'model',
    'rules',
  ]);
  const integrations = new Set(['github', 'gitlab', 'infra']);

  function expectedValid(scopes) {
    const selected = new Set(scopes);
    if (selected.has('cli') && scopes.some(scope => cliForbidden.has(scope))) {
      return false;
    }
    const present = scopes.filter(scope => integrations.has(scope));
    if (present.length > 1) return false;
    if (present.length === 1) {
      const allowed = new Set([present[0], 'docs', 'ci']);
      if (scopes.some(scope => !allowed.has(scope))) return false;
    }
    return true;
  }

  let checked = 0;
  for (let mask = 1; mask < 2 ** EXPECTED_SCOPES.length; mask += 1) {
    const selected = EXPECTED_SCOPES.filter(
      (_, index) => (mask & (1 << index)) !== 0,
    );
    for (const ordered of [selected, [...selected].reverse()]) {
      const scopeList = ordered.join(',');
      if (expectedValid(ordered)) {
        assert.doesNotThrow(() => engine.validateScopeList(scopeList), scopeList);
      } else {
        assert.throws(() => engine.validateScopeList(scopeList), scopeList);
      }
      checked += 1;
    }
  }
  assert.equal(checked, 4094);
});

test('path ownership uses the declarative root contract', () => {
  const cases = new Map([
    ['model/go/dataflow/example/model.go', 'model'],
    ['core/src/test/kotlin/example/ModelTest.kt', 'analyzer'],
    ['core/opentaint-ir/go/tests/src/test/kotlin/IrTest.kt', 'analyzer'],
    ['core/build.gradle.kts', 'core'],
    ['core/opentaint-jvm-autobuilder/src/Main.kt', 'autobuilder'],
    ['rules/ruleset/go/lib/example.yaml', 'rules'],
    ['cli/README.md', 'cli'],
    ['formal/release-scopes/Main.lean', null],
    ['github/action.yml', 'github'],
    ['gitlab/action.yml', 'gitlab'],
    ['infra/pulumi/index.ts', 'infra'],
    ['.github/workflows/ci-rules.yaml', 'ci'],
    ['.github/workflows/ci-analyzer-owasp.yaml', 'ci'],
    ['.github/workflows/ci-github.yaml', 'ci'],
    ['.github/workflows/ci-cli.yaml', 'ci'],
    ['.github/workflows/ci-autobuilder.yaml', 'ci'],
    ['.github/workflows/ci-analyzer.yaml', 'ci'],
    ['.github/workflows/ci-dataflow.yaml', 'ci'],
    ['.github/workflows/ci-ir.yaml', 'ci'],
    ['.github/workflows/release-rules.yaml', 'ci'],
    ['.github/workflows/release-github.yaml', 'ci'],
    ['.github/workflows/release-gitlab.yaml', 'ci'],
    ['.github/workflows/release-cli.yaml', 'ci'],
    ['.github/workflows/publish-autobuilder.yaml', 'ci'],
    ['.github/workflows/publish-analyzer.yaml', 'ci'],
    ['.github/workflows/pr-title.yaml', 'ci'],
    ['cli/.releaserc.cjs', 'ci'],
    ['README.md', 'docs'],
  ]);

  for (const [path, expected] of cases) {
    assert.equal(engine.scopeForPath(path), expected, path);
  }
});

test('every workflow path uses the ci scope', () => {
  const workflows = execFileSync(
    'git',
    ['ls-files', '.github/workflows'],
    { encoding: 'utf8' },
  )
    .trim()
    .split('\n')
    .filter(Boolean);
  assert(workflows.length > 0);
  for (const workflow of workflows) {
    assert.equal(engine.scopeForPath(workflow), 'ci', workflow);
  }
});

test('path ownership rejects an ambiguous refinement', () => {
  const ambiguous = structuredClone(engine.contract);
  ambiguous.ownership.roots.core.rules.push({
    scope: 'autobuilder',
    globs: ['src/**'],
  });
  assert.throws(
    () => engine.scopeForPath('core/src/Main.kt', ambiguous),
    /multiple scopes/,
  );
});

test('exact path validation requires all and only used owners', () => {
  const paths = [
    'model/go/dataflow/example/model.go',
    'core/src/test/kotlin/example/ModelTest.kt',
    'rules/ruleset/go/lib/example.yaml',
  ];
  assert.doesNotThrow(
    () => engine.validateScopePaths('model,analyzer,rules', paths),
  );
  assert.throws(() => engine.validateScopePaths('model', paths));
  assert.throws(
    () => engine.validateScopePaths('model,analyzer,rules,docs', paths),
  );
});

test('every tracked path has one owner or is explicitly ignored', () => {
  const tracked = execFileSync(
    'git',
    ['ls-files', '--cached', '--others', '--exclude-standard'],
    { encoding: 'utf8' },
  )
    .trim()
    .split('\n')
    .filter(candidatePath => candidatePath && fs.existsSync(candidatePath));
  for (const path of tracked) {
    const owner = engine.scopeForPath(path);
    if (owner === null) {
      assert.equal(path.split('/')[0], 'formal', path);
    }
  }
});

test('formal paths are ignored but still require a scoped title', () => {
  const paths = ['formal/go-models/OpenTaint/GoModels/Core.lean'];
  assert.throws(() => engine.validateScopePaths('', paths));
  assert.doesNotThrow(() => engine.validateScopePaths('ci', paths));
});

test('a guarded path cannot omit its scope', () => {
  assert.throws(() => engine.validateScopePaths('', [
    'model/go/dataflow/example/model.go',
  ]));
});

test('ignored formal paths can accompany guarded paths', () => {
  assert.doesNotThrow(() => engine.validateScopePaths('model', [
    'formal/go-models/OpenTaint/GoModels/Core.lean',
    'model/go/dataflow/example/model.go',
  ]));
});

test('pull request title parsing keeps the complete scope list', () => {
  assert.equal(
    engine.scopeListFromTitle('fix(model,analyzer,rules): Update models'),
    'model,analyzer,rules',
  );
  assert.throws(
    () => engine.scopeListFromTitle('chore: Update formal specifications'),
  );
  assert.throws(() => engine.scopeListFromTitle('Update models'));
});

test('release filtering uses scope intersection', () => {
  const subjects = [
    'fix(model,analyzer,rules): Update models',
    'feat(cli): Update the CLI',
    'fix(model): Update one model',
  ];
  assert.deepEqual(
    engine.filterScopedCommits(['analyzer', 'core', 'model'], subjects),
    [subjects[0], subjects[2]],
  );
});
