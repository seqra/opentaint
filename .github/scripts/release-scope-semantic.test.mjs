import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { analyzeCommits } from '@semantic-release/commit-analyzer';

const require = createRequire(import.meta.url);
const {
  RELEASE_PARSER_OPTIONS,
  createReleaseRules,
} = require('./scope-contract.cjs');

const logger = { log() {} };

async function releaseFor(scope, message) {
  return analyzeCommits(
    {
      preset: 'conventionalcommits',
      parserOpts: RELEASE_PARSER_OPTIONS,
      releaseRules: createReleaseRules(scope),
    },
    {
      commits: [{ message }],
      logger,
    },
  );
}

test('real analyzer matches each scope token position', async () => {
  assert.equal(
    await releaseFor('model', 'fix(model, analyzer, rules): Update models'),
    'patch',
  );
  assert.equal(
    await releaseFor('model', 'fix(analyzer, model, rules): Update models'),
    'patch',
  );
  assert.equal(
    await releaseFor('model', 'fix(analyzer, rules, model): Update models'),
    'patch',
  );
});

test('real analyzer keeps legacy compact multi-scope commits', async () => {
  assert.equal(
    await releaseFor('model', 'fix(model,analyzer,rules): Update models'),
    'patch',
  );
});

test('real analyzer keeps release types', async () => {
  assert.equal(
    await releaseFor('rules', 'feat(model, analyzer, rules): Update models'),
    'minor',
  );
  assert.equal(
    await releaseFor('rules', 'fix(model, analyzer, rules): Update models'),
    'patch',
  );
});

test('real analyzer does not release an absent scope', async () => {
  assert.equal(
    await releaseFor('cli', 'fix(model, analyzer, rules): Update models'),
    null,
  );
});

test('real analyzer keeps single-scope compatibility', async () => {
  assert.equal(await releaseFor('rules', 'fix(rules): Update rules'), 'patch');
});

test('real analyzer releases both products for a shared Go IR change', async () => {
  const message = 'fix(analyzer, go-server): Update the shared Go IR protocol';
  assert.equal(await releaseFor('analyzer', message), 'patch');
  assert.equal(await releaseFor('go-server', message), 'patch');
  assert.equal(await releaseFor('autobuilder', message), null);
});
