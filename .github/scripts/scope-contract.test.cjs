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
  'go-server',
  'infra',
  'model',
  'rules',
];

function assertSuggestsExactScopes(scopeList, paths, expectedScopes) {
  const expected = engine.contract.scopes
    .filter(scope => expectedScopes.split(', ').includes(scope))
    .join(', ');
  const expectedSuggestion = `Use exactly these scopes: ${expected}`;
  assert.throws(
    () => engine.validateScopePaths(scopeList, paths),
    error => {
      assert.doesNotMatch(error.message, /Suggested scopes:/);
      const suggestionStart = error.message.indexOf(expectedSuggestion);
      assert.notEqual(suggestionStart, -1, error.message);
      assert.equal(error.message.slice(suggestionStart), expectedSuggestion);
      return true;
    },
  );
}

test('the contract has one ordered scope declaration', () => {
  assert.deepEqual(engine.contract.scopes, EXPECTED_SCOPES);
  assert.doesNotThrow(() => engine.validateContract(engine.contract));
});

test('scope validation is independent of scope order', () => {
  assert.deepEqual(
    engine.validateScopeList('rules, model, analyzer'),
    ['rules', 'model', 'analyzer'],
  );
  assert.deepEqual(
    engine.validateScopeList('analyzer, model, rules'),
    ['analyzer', 'model', 'rules'],
  );
});

test('scope validation rejects duplicates and unknown scopes', () => {
  assert.throws(() => engine.validateScopeList(''));
  assert.throws(() => engine.validateScopeList('model, model'));
  assert.throws(() => engine.validateScopeList('formal'));
  assert.throws(() => engine.validateScopeList('model, unknown'));
  assert.throws(() => engine.validateScopeList('model,,rules'));
});

test('multi-scope validation requires one space after each comma', () => {
  assert.doesNotThrow(() => engine.validateScopeList('core, model'));
  assert.throws(() => engine.validateScopeList('core,model'));
  assert.throws(() => engine.validateScopeList('core,  model'));
  assert.throws(() => engine.validateScopeList('core , model'));
});

test('cli cannot occur with release component scopes', () => {
  for (const forbidden of [
    'analyzer',
    'autobuilder',
    'core',
    'go-server',
    'model',
    'rules',
  ]) {
    assert.throws(() => engine.validateScopeList(`cli, ${forbidden}`));
  }
  assert.doesNotThrow(() => engine.validateScopeList('cli, docs'));
  assert.doesNotThrow(() => engine.validateScopeList('cli, ci'));
});

test('repository integration scopes are mutually exclusive', () => {
  for (const pair of [
    'github, gitlab',
    'github, infra',
    'gitlab, infra',
    'github, gitlab, docs, ci',
  ]) {
    assert.throws(() => engine.validateScopeList(pair));
  }
});

test('repository integration scopes permit docs and ci companions', () => {
  for (const scope of ['github', 'gitlab', 'infra']) {
    assert.doesNotThrow(() => engine.validateScopeList(scope));
    assert.doesNotThrow(() => engine.validateScopeList(`${scope}, docs`));
    assert.doesNotThrow(() => engine.validateScopeList(`ci, ${scope}`));
    assert.doesNotThrow(() => engine.validateScopeList(`${scope}, docs, ci`));
    assert.throws(() => engine.validateScopeList(`${scope}, model`));
  }
});

test('all scope subsets agree with the formal compatibility policy', () => {
  const cliForbidden = new Set([
    'analyzer',
    'autobuilder',
    'core',
    'go-server',
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
  let validSets = 0;
  for (let mask = 1; mask < 2 ** EXPECTED_SCOPES.length; mask += 1) {
    const selected = EXPECTED_SCOPES.filter(
      (_, index) => (mask & (1 << index)) !== 0,
    );
    if (expectedValid(selected)) validSets += 1;
    for (const ordered of [selected, [...selected].reverse()]) {
      const scopeList = ordered.join(', ');
      if (expectedValid(ordered)) {
        assert.doesNotThrow(() => engine.validateScopeList(scopeList), scopeList);
      } else {
        assert.throws(() => engine.validateScopeList(scopeList), scopeList);
      }
      checked += 1;
    }
  }
  assert.equal(checked, 8190);
  assert.equal(validSets, 271);
});

test('path ownership uses the declarative root contract', () => {
  const cases = new Map([
    ['model/go/dataflow/example/model.go', ['model']],
    ['core/src/test/kotlin/example/ModelTest.kt', ['core', 'analyzer']],
    [
      'core/opentaint-ir/go/tests/src/test/kotlin/IrTest.kt',
      ['core', 'analyzer'],
    ],
    ['core/build.gradle.kts', ['core']],
    [
      'core/opentaint-jvm-autobuilder/src/Main.kt',
      ['core', 'autobuilder'],
    ],
    ['core/opentaint-project-model/src/Project.kt', ['core']],
    ['core/opentaint-utils/cli-util/src/Cli.kt', ['core']],
    [
      'core/opentaint-ir/go/go-ir-api/src/Program.kt',
      ['core', 'analyzer'],
    ],
    [
      'core/opentaint-ir/go/go-ssa-server/server.go',
      ['core', 'go-server'],
    ],
    [
      'core/opentaint-ir/go/proto/goir/service.proto',
      ['core', 'analyzer', 'go-server'],
    ],
    [
      'core/opentaint-dataflow-core/opentaint-go-dataflow/src/Dataflow.kt',
      ['core', 'analyzer'],
    ],
    ['rules/ruleset/go/lib/example.yaml', ['rules']],
    ['cli/README.md', ['cli']],
    ['formal/release-scopes/Main.lean', null],
    ['github/action.yml', ['github']],
    ['gitlab/action.yml', ['gitlab']],
    ['infra/pulumi/index.ts', ['infra']],
    ['.github/workflows/ci-rules.yaml', ['ci']],
    ['.github/workflows/ci-analyzer-owasp.yaml', ['ci']],
    ['.github/workflows/ci-github.yaml', ['ci']],
    ['.github/workflows/ci-cli.yaml', ['ci']],
    ['.github/workflows/ci-autobuilder.yaml', ['ci']],
    ['.github/workflows/ci-analyzer.yaml', ['ci']],
    ['.github/workflows/ci-dataflow.yaml', ['ci']],
    ['.github/workflows/ci-ir.yaml', ['ci']],
    ['.github/workflows/release-rules.yaml', ['ci']],
    ['.github/workflows/release-github.yaml', ['ci']],
    ['.github/workflows/release-gitlab.yaml', ['ci']],
    ['.github/workflows/release-cli.yaml', ['ci']],
    ['.github/workflows/publish-autobuilder.yaml', ['ci']],
    ['.github/workflows/publish-analyzer.yaml', ['ci']],
    ['.github/workflows/pr-title.yaml', ['ci']],
    ['cli/.releaserc.cjs', ['ci']],
    ['README.md', ['docs']],
  ]);

  for (const [path, expected] of cases) {
    assert.deepEqual(engine.requiredScopesForPath(path), expected, path);
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
    assert.deepEqual(engine.requiredScopesForPath(workflow), ['ci'], workflow);
  }
});

test('path ownership rejects an ambiguous refinement', () => {
  const ambiguous = structuredClone(engine.contract);
  ambiguous.ownership.roots.core.rules.push({
    requiredScopes: ['autobuilder'],
    globs: ['src/**'],
  });
  assert.throws(
    () => engine.requiredScopesForPath('core/src/Main.kt', ambiguous),
    /multiple scope requirements/,
  );
});

test('path ownership rejects an incompatible requirement set', () => {
  const incompatible = structuredClone(engine.contract);
  incompatible.ownership.roots.core.rules.push({
    requiredScopes: ['cli', 'analyzer'],
    globs: ['new-component/**'],
  });
  assert.throws(
    () => engine.validateContract(incompatible),
    /cli scope cannot occur with the analyzer scope/,
  );
});

test('path ownership rejects incompatible additive default and refinement scopes', () => {
  const incompatible = structuredClone(engine.contract);
  incompatible.ownership.roots.core.rules.push({
    requiredScopes: ['cli'],
    globs: ['cli-only/**'],
  });
  assert.throws(
    () => engine.validateContract(incompatible),
    /cli scope cannot occur with the core scope/,
  );
});

test('path ownership rejects malformed requirement sets', () => {
  for (const requiredScopes of [[], ['core', 'core'], ['unknown']]) {
    const malformed = structuredClone(engine.contract);
    malformed.ownership.roots.core.defaultScopes = requiredScopes;
    assert.throws(() => engine.validateContract(malformed));
  }
});

test('a shared Go IR protocol path requires core and both product scopes', () => {
  const paths = ['core/opentaint-ir/go/proto/goir/service.proto'];
  assert.doesNotThrow(
    () => engine.validateScopePaths('core, analyzer, go-server', paths),
  );
  assert.doesNotThrow(
    () => engine.validateScopePaths('go-server, analyzer, core', paths),
  );
  assertSuggestsExactScopes(
    'analyzer, go-server',
    paths,
    'core, analyzer, go-server',
  );
  assertSuggestsExactScopes(
    'core, analyzer',
    paths,
    'core, analyzer, go-server',
  );
  assert.throws(() => engine.validateScopePaths('ir', paths));
});

test('exact path validation requires all and only used owners', () => {
  const paths = [
    'model/go/dataflow/example/model.go',
    'core/src/test/kotlin/example/ModelTest.kt',
    'rules/ruleset/go/lib/example.yaml',
  ];
  assert.doesNotThrow(
    () => engine.validateScopePaths('model, core, analyzer, rules', paths),
  );
  assertSuggestsExactScopes(
    'model, rules',
    paths,
    'model, core, analyzer, rules',
  );
  assertSuggestsExactScopes(
    'model, core, analyzer, rules, docs',
    paths,
    'model, core, analyzer, rules',
  );
});

test('core paths follow analyzer and autobuilder release effects', () => {
  assertSuggestsExactScopes('analyzer, model', [
    'core/samples/src/main/java/test/samples/DataFlowBenchCallbackSample.java',
    'model/go/dataflow/example/model.go',
  ], 'core, analyzer, model');
  assertSuggestsExactScopes('core, model', [
    'core/samples/src/main/java/test/samples/DataFlowBenchCallbackSample.java',
    'model/go/dataflow/example/model.go',
  ], 'core, analyzer, model');
  assert.doesNotThrow(() => engine.validateScopePaths('core, model', [
    'core/opentaint-project-model/src/main/kotlin/Project.kt',
    'model/go/dataflow/example/model.go',
  ]));
});

test('direct component paths always require their own scope', () => {
  const cases = [
    {
      path: 'core/samples/src/main/java/test/samples/DataFlowBenchCallbackSample.java',
      scopes: ['core', 'analyzer'],
      aliases: ['analyzer', 'core', 'model'],
    },
    {
      path: 'core/opentaint-jvm-autobuilder/src/Main.kt',
      scopes: ['core', 'autobuilder'],
      aliases: ['autobuilder', 'core', 'analyzer'],
    },
    {
      path: 'core/opentaint-ir/go/go-ssa-server/server.go',
      scopes: ['core', 'go-server'],
      aliases: ['go-server', 'core', 'analyzer'],
    },
    {
      path: 'model/go/dataflow/example/model.go',
      scopes: ['model'],
      aliases: ['analyzer', 'core'],
    },
  ];

  for (const { path, scopes, aliases } of cases) {
    const expected = scopes.join(', ');
    assert.doesNotThrow(
      () => engine.validateScopePaths(expected, [path]),
      `${path} must accept ${expected}`,
    );
    for (const alias of aliases) {
      assertSuggestsExactScopes(alias, [path], expected);
      if (!scopes.includes(alias)) {
        assertSuggestsExactScopes(
          `${expected}, ${alias}`,
          [path],
          expected,
        );
      }
    }
  }
});

test('scope mismatch suggestions aggregate and order every path owner', () => {
  const paths = [
    'core/samples/src/main/java/test/samples/DataFlowBenchCallbackSample.java',
    'core/opentaint-jvm-autobuilder/src/Main.kt',
    'model/go/dataflow/example/model.go',
  ];

  assertSuggestsExactScopes(
    'core, model, docs',
    paths,
    'core, analyzer, autobuilder, model',
  );
  assertSuggestsExactScopes(
    'model, core, analyzer, autobuilder, docs',
    paths,
    'core, analyzer, autobuilder, model',
  );
  assert.doesNotThrow(() => engine.validateScopePaths(
    'core, analyzer, autobuilder, model',
    paths,
  ));
});

test('release scope sets encode scope release effects', () => {
  assert.deepEqual(
    engine.scopesForRelease('analyzer'),
    ['analyzer', 'core', 'model'],
  );
  assert.deepEqual(
    engine.scopesForRelease('autobuilder'),
    ['autobuilder', 'core'],
  );
  assert.deepEqual(
    engine.scopesForRelease('go-server'),
    ['go-server'],
  );
  assert.throws(() => engine.scopesForRelease('unknown'));
});

test('every tracked path has one requirement set or is explicitly ignored', () => {
  const tracked = execFileSync(
    'git',
    ['ls-files', '--cached', '--others', '--exclude-standard'],
    { encoding: 'utf8' },
  )
    .trim()
    .split('\n')
    .filter(candidatePath => candidatePath && fs.existsSync(candidatePath));
  for (const path of tracked) {
    const requiredScopes = engine.requiredScopesForPath(path);
    if (requiredScopes === null) {
      assert.equal(path.split('/')[0], 'formal', path);
    }
  }
});

test('formal paths are ignored but still require a scoped title', () => {
  const paths = ['formal/go-models/OpenTaint/GoModels/Core.lean'];
  assert.throws(() => engine.validateScopePaths('', paths));
  assert.doesNotThrow(() => engine.validateScopePaths('ci', paths));
  assert.throws(() => engine.validateScopePaths('core', paths));
  assert.throws(() => engine.validateScopePaths('docs', paths));
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
    engine.scopeListFromTitle('fix(model, analyzer, rules): Update models'),
    'model, analyzer, rules',
  );
  assert.throws(
    () => engine.scopeListFromTitle('chore: Update formal specifications'),
  );
  assert.throws(() => engine.scopeListFromTitle('Update models'));
});

test('release filtering uses scope intersection', () => {
  const subjects = [
    'fix(model, analyzer, rules): Update models',
    'feat(cli): Update the CLI',
    'fix(model): Update one model',
  ];
  assert.deepEqual(
    engine.filterScopedCommits(['analyzer', 'core', 'model'], subjects),
    [subjects[0], subjects[2]],
  );
});
