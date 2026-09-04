'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');

const {
  RELEASE_PARSER_OPTIONS,
  createReleaseRules,
  hasAnyScope,
  scopesForRelease,
  scopeExclusionPattern,
  scopePatterns,
  splitScopes,
} = require('./scope-contract.cjs');
const { createTransform } = require('../../release-notes-transform.cjs');

test('splitScopes keeps ordered scope tokens', () => {
  assert.deepEqual(
    splitScopes('model, analyzer, rules'),
    ['model', 'analyzer', 'rules'],
  );
  assert.deepEqual(
    splitScopes('model,analyzer,rules'),
    ['model', 'analyzer', 'rules'],
  );
});

test('release parser accepts a comma-separated scope list', () => {
  const parsed = RELEASE_PARSER_OPTIONS.headerPattern.exec(
    'fix(model, analyzer, rules): Update models',
  );
  assert.notEqual(parsed, null);
  assert.deepEqual(parsed.slice(1), [
    'fix',
    'model, analyzer, rules',
    'Update models',
  ]);
});

test('release matching uses scope intersection', () => {
  assert.equal(
    hasAnyScope('model, analyzer, rules', ['analyzer', 'core', 'model']),
    true,
  );
  assert.equal(hasAnyScope('model, analyzer, rules', ['rules']), true);
  assert.equal(hasAnyScope('model, analyzer, rules', ['cli']), false);
});

test('release mappings use product scopes for shared Go IR changes', () => {
  assert.equal(hasAnyScope('core', scopesForRelease('analyzer')), true);
  assert.equal(hasAnyScope('core', scopesForRelease('autobuilder')), true);
  assert.equal(hasAnyScope('core', scopesForRelease('go-server')), false);
  assert.equal(hasAnyScope('analyzer', scopesForRelease('autobuilder')), false);
  assert.equal(hasAnyScope('autobuilder', scopesForRelease('analyzer')), false);
  assert.equal(hasAnyScope('go-server', scopesForRelease('analyzer')), false);
  assert.equal(hasAnyScope('go-server', scopesForRelease('go-server')), true);
  assert.equal(
    hasAnyScope('analyzer, go-server', scopesForRelease('analyzer')),
    true,
  );
  assert.equal(
    hasAnyScope('analyzer, go-server', scopesForRelease('go-server')),
    true,
  );
  assert.equal(
    hasAnyScope('analyzer, go-server', scopesForRelease('autobuilder')),
    false,
  );
  assert.equal(hasAnyScope('model', scopesForRelease('analyzer')), true);
  assert.equal(hasAnyScope('model', scopesForRelease('autobuilder')), false);
  assert.equal(hasAnyScope('model', scopesForRelease('go-server')), false);
});

test('publish workflows select a release instead of repeating scope sets', () => {
  const action = fs.readFileSync('.github/actions/check-scoped-commits/action.yml', 'utf8');
  const analyzer = fs.readFileSync('.github/workflows/publish-analyzer.yaml', 'utf8');
  const autobuilder = fs.readFileSync('.github/workflows/publish-autobuilder.yaml', 'utf8');
  const goServer = fs.readFileSync('.github/workflows/publish-go-server.yaml', 'utf8');
  const releaseCi = fs.readFileSync('.github/workflows/ci-release-contract.yaml', 'utf8');
  assert.match(action, /release-scopes "\$RELEASE"/);
  assert.match(analyzer, /release: analyzer/);
  assert.match(autobuilder, /release: autobuilder/);
  assert.doesNotMatch(analyzer, /scopes: analyzer,core,model/);
  assert.doesNotMatch(autobuilder, /scopes: autobuilder,core/);
  assert.match(goServer, /release: go-server/);
  assert.doesNotMatch(goServer, /scopes: go-server,core/);
  assert.equal(
    releaseCi.match(/\.github\/workflows\/publish-\*\.yaml/g)?.length,
    2,
  );
});

test('scoped commit action sets up Node before invoking the contract', () => {
  const action = fs.readFileSync('.github/actions/check-scoped-commits/action.yml', 'utf8');
  const setupNode = action.indexOf('uses: actions/setup-node@');
  const contractInvocation = action.indexOf(
    'node "$GITHUB_WORKSPACE/.github/scripts/scope-contract.cjs"',
  );

  assert.notEqual(setupNode, -1);
  assert.notEqual(contractInvocation, -1);
  assert.ok(setupNode < contractInvocation);
});

test('scope patterns match each token position', () => {
  assert.deepEqual(
    scopePatterns('rules'),
    [
      'rules',
      'rules, *',
      '*, rules',
      '*, rules, *',
      'rules,*',
      '*,rules',
      '*,rules,*',
    ],
  );
});

test('release rules include every token position and an exact exclusion', () => {
  const rules = createReleaseRules('rules');
  assert.equal(
    rules.some(rule =>
      rule.scope === '*, rules, *' && rule.type === 'feat' && rule.release === 'minor'
    ),
    true,
  );
  assert.equal(
    rules.some(rule =>
      rule.scope === scopeExclusionPattern('rules') && rule.release === false
    ),
    true,
  );
});

function commit(scope) {
  return {
    scope,
    type: 'fix',
    notes: [],
    hash: '1234567890',
    subject: 'Update release matching',
    references: [],
  };
}

test('release notes include a commit with an allowed scope token', () => {
  const transformed = createTransform(['rules'])(
    commit('model, analyzer, rules'),
    {},
  );
  assert.notEqual(transformed, null);
});

test('release notes exclude a commit without an allowed scope token', () => {
  const transformed = createTransform(['cli'])(
    commit('model, analyzer, rules'),
    {},
  );
  assert.equal(transformed, null);
});
