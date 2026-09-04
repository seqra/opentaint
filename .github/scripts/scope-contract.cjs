'use strict';

const fs = require('node:fs');
const path = require('node:path');

const contractPath = path.join(__dirname, '..', 'scope-contract.json');
const contract = JSON.parse(fs.readFileSync(contractPath, 'utf8'));

const RELEASE_TYPES = Object.freeze([
  ['feat', 'minor'],
  ['fix', 'patch'],
  ['refactor', 'patch'],
  ['revert', 'patch'],
]);

const RELEASE_PARSER_OPTIONS = Object.freeze({
  headerPattern: /^(\w*)(?:\(([^)]*)\))?!?: (.*)$/,
  headerCorrespondence: ['type', 'scope', 'subject'],
});

class ScopeContractError extends Error {}

function assert(condition, message) {
  if (!condition) throw new ScopeContractError(message);
}

function assertScope(scope, knownScopes, location) {
  assert(
    typeof scope === 'string' && knownScopes.has(scope),
    `${location} refers to unknown scope '${scope}'`,
  );
}

function validateRequiredScopes(scopes, knownScopes, location) {
  assert(
    Array.isArray(scopes) && scopes.length > 0,
    `${location} must be a non-empty array`,
  );
  assert(new Set(scopes).size === scopes.length, `${location} must be unique`);
  for (const scope of scopes) assertScope(scope, knownScopes, location);
}

function validateScopeCompatibility(scopes, candidate) {
  const selected = new Set(scopes);
  for (const [left, right] of candidate.compatibility.forbiddenPairs) {
    assert(
      !selected.has(left) || !selected.has(right),
      `The ${left} scope cannot occur with the ${right} scope`,
    );
  }
  for (const group of candidate.compatibility.exclusiveGroups) {
    const present = group.filter(scope => selected.has(scope));
    assert(
      present.length < 2,
      `These scopes are mutually exclusive: ${present.join(',')}`,
    );
  }
  for (const [scope, companions] of Object.entries(
    candidate.compatibility.companions,
  )) {
    if (!selected.has(scope)) continue;
    const allowed = new Set([scope, ...companions]);
    const invalid = scopes.filter(other => !allowed.has(other));
    assert(
      invalid.length === 0,
      `The ${scope} scope cannot occur with ${invalid.join(',')}`,
    );
  }
}

function validateRule(rule, knownScopes, location) {
  assert(rule && typeof rule === 'object', `${location} must be an object`);
  validateRequiredScopes(
    rule.requiredScopes,
    knownScopes,
    `${location}.requiredScopes`,
  );
  assert(
    Array.isArray(rule.globs) && rule.globs.length > 0,
    `${location}.globs must be a non-empty array`,
  );
  for (const glob of rule.globs) {
    assert(
      typeof glob === 'string' && glob.length > 0,
      `${location}.globs must contain non-empty strings`,
    );
  }
  if (rule.excludeGlobs !== undefined) {
    assert(
      Array.isArray(rule.excludeGlobs) && rule.excludeGlobs.length > 0,
      `${location}.excludeGlobs must be a non-empty array`,
    );
    assert(
      new Set(rule.excludeGlobs).size === rule.excludeGlobs.length,
      `${location}.excludeGlobs must be unique`,
    );
    for (const glob of rule.excludeGlobs) {
      assert(
        typeof glob === 'string' && glob.length > 0,
        `${location}.excludeGlobs must contain non-empty strings`,
      );
    }
  }
}

function validateContract(candidate) {
  assert(candidate && typeof candidate === 'object', 'The contract must be an object');
  assert(candidate.schemaVersion === 2, 'The contract schema version must be 2');
  assert(Array.isArray(candidate.scopes), 'The contract scopes must be an array');

  const knownScopes = new Set(candidate.scopes);
  assert(knownScopes.size === candidate.scopes.length, 'Contract scopes must be unique');
  for (const scope of candidate.scopes) {
    assert(typeof scope === 'string' && scope.length > 0, 'Scopes must be non-empty strings');
  }

  const compatibility = candidate.compatibility;
  assert(compatibility && typeof compatibility === 'object', 'Compatibility is required');
  for (const [index, pair] of compatibility.forbiddenPairs.entries()) {
    assert(Array.isArray(pair) && pair.length === 2, `forbiddenPairs[${index}] must contain two scopes`);
    assertScope(pair[0], knownScopes, `forbiddenPairs[${index}]`);
    assertScope(pair[1], knownScopes, `forbiddenPairs[${index}]`);
    assert(pair[0] !== pair[1], `forbiddenPairs[${index}] must contain different scopes`);
  }
  for (const [index, group] of compatibility.exclusiveGroups.entries()) {
    assert(Array.isArray(group) && group.length > 1, `exclusiveGroups[${index}] must contain two or more scopes`);
    assert(new Set(group).size === group.length, `exclusiveGroups[${index}] must be unique`);
    for (const scope of group) assertScope(scope, knownScopes, `exclusiveGroups[${index}]`);
  }
  for (const [scope, companions] of Object.entries(compatibility.companions)) {
    assertScope(scope, knownScopes, 'companions');
    assert(Array.isArray(companions), `Companions for '${scope}' must be an array`);
    assert(new Set(companions).size === companions.length, `Companions for '${scope}' must be unique`);
    for (const companion of companions) assertScope(companion, knownScopes, `companions.${scope}`);
  }

  assert(
    candidate.releaseScopes && typeof candidate.releaseScopes === 'object',
    'Release scope sets are required',
  );
  for (const [release, scopes] of Object.entries(candidate.releaseScopes)) {
    assert(release.length > 0, 'Release names must be non-empty strings');
    validateRequiredScopes(scopes, knownScopes, `releaseScopes.${release}`);
  }

  const ownership = candidate.ownership;
  assert(ownership && typeof ownership === 'object', 'Ownership is required');
  assert(Array.isArray(ownership.ignoredRoots), 'Ignored ownership roots must be an array');
  assert(
    new Set(ownership.ignoredRoots).size === ownership.ignoredRoots.length,
    'Ignored ownership roots must be unique',
  );
  for (const root of ownership.ignoredRoots) {
    assert(
      typeof root === 'string' && root.length > 0 && !root.includes('/'),
      `Invalid ignored ownership root '${root}'`,
    );
    assert(
      !Object.hasOwn(ownership.roots, root),
      `Ignored ownership root '${root}' also has an owner`,
    );
  }
  for (const [index, rule] of ownership.overrides.entries()) {
    validateRule(rule, knownScopes, `ownership.overrides[${index}]`);
    validateScopeCompatibility(rule.requiredScopes, candidate);
  }
  for (const [root, route] of Object.entries(ownership.roots)) {
    assert(root.length > 0 && !root.includes('/'), `Invalid ownership root '${root}'`);
    validateRequiredScopes(
      route.defaultScopes,
      knownScopes,
      `ownership.roots.${root}.defaultScopes`,
    );
    validateScopeCompatibility(route.defaultScopes, candidate);
    for (const [index, rule] of (route.rules || []).entries()) {
      validateRule(rule, knownScopes, `ownership.roots.${root}.rules[${index}]`);
      validateScopeCompatibility(rule.requiredScopes, candidate);
    }
  }
  const documentation = ownership.documentation;
  assert(documentation && typeof documentation === 'object', 'Documentation ownership is required');
  validateRequiredScopes(
    documentation.requiredScopes,
    knownScopes,
    'ownership.documentation.requiredScopes',
  );
  validateScopeCompatibility(documentation.requiredScopes, candidate);
  for (const key of ['rootDirectories', 'basenames', 'extensions', 'rootFiles']) {
    assert(Array.isArray(documentation[key]), `ownership.documentation.${key} must be an array`);
    assert(new Set(documentation[key]).size === documentation[key].length, `ownership.documentation.${key} must be unique`);
  }

  return candidate;
}

function globToRegExp(glob) {
  let expression = '^';
  for (let index = 0; index < glob.length; index += 1) {
    const character = glob[index];
    if (character === '*' && glob[index + 1] === '*') {
      if (glob[index + 2] === '/') {
        expression += '(?:.*/)?';
        index += 2;
      } else {
        expression += '.*';
        index += 1;
      }
    } else if (character === '*') {
      expression += '[^/]*';
    } else if (character === '?') {
      expression += '[^/]';
    } else {
      expression += character.replace(/[|\\{}()[\]^$+?.]/g, '\\$&');
    }
  }
  return new RegExp(`${expression}$`);
}

function ruleMatches(rule, candidatePath) {
  const included = rule.globs.some(glob => globToRegExp(glob).test(candidatePath));
  const excluded = (rule.excludeGlobs || [])
    .some(glob => globToRegExp(glob).test(candidatePath));
  return included && !excluded;
}

function oneRuleRequirements(rules, candidatePath, location) {
  const matches = rules.filter(rule => ruleMatches(rule, candidatePath));
  if (matches.length > 1) {
    const requirements = matches
      .map(rule => `{${rule.requiredScopes.join(', ')}}`)
      .join(', ');
    throw new ScopeContractError(
      `${location} has multiple scope requirements: ${requirements}`,
    );
  }
  return matches.length === 1 ? matches[0].requiredScopes : undefined;
}

function splitScopes(scopeList) {
  if (typeof scopeList !== 'string' || scopeList.length === 0) return [];
  return scopeList.split(',').map(scope => scope.trim());
}

function validateScopeList(scopeList, candidate = contract) {
  validateContract(candidate);
  assert(typeof scopeList === 'string' && scopeList.length > 0, 'A scope list is required');
  assert(
    /^[^,\s]+(?:, [^,\s]+)*$/.test(scopeList),
    'Separate scopes with one comma and one space',
  );
  const scopes = splitScopes(scopeList);
  assert(scopes.every(Boolean), 'Scope lists cannot contain an empty scope');

  const knownScopes = new Set(candidate.scopes);
  const selected = new Set();
  for (const scope of scopes) {
    assert(knownScopes.has(scope), `Unknown scope: ${scope}`);
    assert(!selected.has(scope), `Scope occurs more than once: ${scope}`);
    selected.add(scope);
  }

  validateScopeCompatibility(scopes, candidate);

  return scopes;
}

function requiredScopesForPath(candidatePath, candidate = contract) {
  validateContract(candidate);
  assert(typeof candidatePath === 'string' && candidatePath.length > 0, 'A changed path is required');
  assert(!candidatePath.startsWith('/'), `Changed paths must be relative: ${candidatePath}`);
  assert(!candidatePath.includes('\\'), `Changed paths must use forward slashes: ${candidatePath}`);
  assert(!candidatePath.split('/').includes('..'), `Changed paths cannot contain '..': ${candidatePath}`);

  const separator = candidatePath.indexOf('/');
  const root = separator === -1 ? candidatePath : candidatePath.slice(0, separator);
  const relative = separator === -1 ? '' : candidatePath.slice(separator + 1);
  if (candidate.ownership.ignoredRoots.includes(root)) return null;

  const override = oneRuleRequirements(
    candidate.ownership.overrides,
    candidatePath,
    candidatePath,
  );
  if (override) return [...override];

  const route = candidate.ownership.roots[root];
  if (route) {
    const refined = oneRuleRequirements(route.rules || [], relative, candidatePath);
    return [...(refined || route.defaultScopes)];
  }

  const docs = candidate.ownership.documentation;
  const basename = path.posix.basename(candidatePath);
  const extension = path.posix.extname(candidatePath);
  if (
    docs.rootDirectories.includes(root) ||
    docs.basenames.includes(basename) ||
    docs.extensions.includes(extension) ||
    docs.rootFiles.includes(candidatePath)
  ) {
    return [...docs.requiredScopes];
  }

  throw new ScopeContractError(`No scope owns changed path: ${candidatePath}`);
}

function validateScopePaths(scopeList, paths, candidate = contract) {
  const scopes = validateScopeList(scopeList, candidate);
  assert(Array.isArray(paths), 'Changed paths must be an array');
  assert(paths.length > 0, 'At least one changed path is required');
  const requirements = paths.map(
    changedPath => requiredScopesForPath(changedPath, candidate),
  );
  const guardedRequirements = requirements.filter(required => required !== null);
  if (guardedRequirements.length === 0) {
    assert(
      scopes.length === 1 && scopes[0] === 'ci',
      'An ignored-only change must use only the ci scope',
    );
    return scopes;
  }

  const selected = new Set(scopes);
  const used = new Set();

  for (let index = 0; index < paths.length; index += 1) {
    const changedPath = paths[index];
    const required = requirements[index];
    if (required === null) continue;
    for (const scope of required) {
      assert(
        selected.has(scope),
        `Changed path '${changedPath}' requires scope '${scope}'`,
      );
      used.add(scope);
    }
  }
  for (const scope of scopes) {
    assert(used.has(scope), `Scope '${scope}' does not own a changed path`);
  }
  return scopes;
}

function hasAnyScope(scopeList, allowedScopes) {
  const scopes = new Set(splitScopes(scopeList));
  return allowedScopes.some(scope => scopes.has(scope));
}

function scopesForRelease(release, candidate = contract) {
  validateContract(candidate);
  assert(
    typeof release === 'string' && Object.hasOwn(candidate.releaseScopes, release),
    `Unknown release: ${release}`,
  );
  return [...candidate.releaseScopes[release]];
}

function scopePatterns(scope) {
  return [
    scope,
    `${scope}, *`,
    `*, ${scope}`,
    `*, ${scope}, *`,
    `${scope},*`,
    `*,${scope}`,
    `*,${scope},*`,
  ];
}

function scopeExclusionPattern(scope) {
  return `!(${scopePatterns(scope).join('|')})`;
}

function createReleaseRules(scope) {
  const rules = [];
  for (const pattern of scopePatterns(scope)) {
    rules.push({ scope: pattern, breaking: true, release: 'major' });
    for (const [type, release] of RELEASE_TYPES) {
      rules.push({ scope: pattern, type, release });
    }
  }
  rules.push({ scope: scopeExclusionPattern(scope), release: false });
  return rules;
}

function scopeListFromTitle(subject) {
  const match = /^(?:chore|feat|fix|refactor|revert|style|test)\(([^()]*)\)!?:\s/.exec(subject);
  assert(match, `Could not extract scopes from title: ${subject}`);
  validateScopeList(match[1]);
  return match[1];
}

function commitScopeList(subject) {
  const match = /^[a-z]+\(([^()]*)\)!?:\s/.exec(subject);
  return match ? match[1] : undefined;
}

function filterScopedCommits(releaseScopes, subjects) {
  const allowed = Array.isArray(releaseScopes) ? releaseScopes : splitScopes(releaseScopes);
  return subjects.filter(subject => {
    const scopes = commitScopeList(subject);
    return scopes !== undefined && hasAnyScope(scopes, allowed);
  });
}

function readStandardInput() {
  return fs.readFileSync(0, 'utf8').split('\n').filter(Boolean);
}

function runCli(argv) {
  const [command, argument] = argv;
  if (command === 'validate-paths') {
    validateScopePaths(argument, readStandardInput());
    return;
  }
  if (command === 'validate-list') {
    validateScopeList(argument);
    return;
  }
  if (command === 'scope-for-path' || command === 'scopes-for-path') {
    const required = requiredScopesForPath(argument);
    process.stdout.write(`${required === null ? 'ignored' : required.join(', ')}\n`);
    return;
  }
  if (command === 'title-scopes') {
    process.stdout.write(`${scopeListFromTitle(argument)}\n`);
    return;
  }
  if (command === 'filter-commits') {
    const matches = filterScopedCommits(splitScopes(argument), readStandardInput());
    if (matches.length > 0) process.stdout.write(`${matches.join('\n')}\n`);
    return;
  }
  if (command === 'release-scopes') {
    process.stdout.write(`${scopesForRelease(argument).join(', ')}\n`);
    return;
  }
  throw new ScopeContractError(
    'Usage: scope-contract.cjs validate-paths|validate-list|scopes-for-path|title-scopes|filter-commits|release-scopes ARGUMENT',
  );
}

validateContract(contract);

if (require.main === module) {
  try {
    runCli(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`${error.message}\n`);
    process.exitCode = 1;
  }
}

module.exports = {
  RELEASE_PARSER_OPTIONS,
  ScopeContractError,
  commitScopeList,
  contract,
  createReleaseRules,
  filterScopedCommits,
  globToRegExp,
  hasAnyScope,
  requiredScopesForPath,
  runCli,
  scopesForRelease,
  scopeExclusionPattern,
  scopeListFromTitle,
  scopePatterns,
  splitScopes,
  validateContract,
  validateScopeList,
  validateScopePaths,
};
