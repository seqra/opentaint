'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const {
  RELEASE_PARSER_OPTIONS,
  createReleaseRules,
  hasAnyScope,
  scopeExclusionPattern,
  scopePatterns,
  splitScopes,
} = require('./scope-contract.cjs');
const { createTransform } = require('../../release-notes-transform.cjs');

test('splitScopes keeps ordered scope tokens', () => {
  assert.deepEqual(
    splitScopes('model,analyzer,rules'),
    ['model', 'analyzer', 'rules'],
  );
});

test('release parser accepts a comma-separated scope list', () => {
  const parsed = RELEASE_PARSER_OPTIONS.headerPattern.exec(
    'fix(model,analyzer,rules): Update models',
  );
  assert.notEqual(parsed, null);
  assert.deepEqual(parsed.slice(1), [
    'fix',
    'model,analyzer,rules',
    'Update models',
  ]);
});

test('release matching uses scope intersection', () => {
  assert.equal(
    hasAnyScope('model,analyzer,rules', ['analyzer', 'core', 'model']),
    true,
  );
  assert.equal(hasAnyScope('model,analyzer,rules', ['rules']), true);
  assert.equal(hasAnyScope('model,analyzer,rules', ['cli']), false);
});

test('scope patterns match each token position', () => {
  assert.deepEqual(
    scopePatterns('rules'),
    ['rules', 'rules,*', '*,rules', '*,rules,*'],
  );
});

test('release rules include every token position and an exact exclusion', () => {
  const rules = createReleaseRules('rules');
  assert.equal(
    rules.some(rule =>
      rule.scope === '*,rules,*' && rule.type === 'feat' && rule.release === 'minor'
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
    commit('model,analyzer,rules'),
    {},
  );
  assert.notEqual(transformed, null);
});

test('release notes exclude a commit without an allowed scope token', () => {
  const transformed = createTransform(['cli'])(
    commit('model,analyzer,rules'),
    {},
  );
  assert.equal(transformed, null);
});
