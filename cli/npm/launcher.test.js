'use strict';

const test = require('node:test');
const assert = require('node:assert');
const path = require('node:path');

const {
  platformPackage,
  resolveBinary,
  signalExitCode,
  run,
} = require('./bin/opentaint.js');

test('platformPackage maps every supported platform/arch', () => {
  assert.strictEqual(platformPackage('linux', 'x64'), '@seqra/opentaint-linux-x64');
  assert.strictEqual(platformPackage('linux', 'arm64'), '@seqra/opentaint-linux-arm64');
  assert.strictEqual(platformPackage('darwin', 'x64'), '@seqra/opentaint-darwin-x64');
  assert.strictEqual(platformPackage('darwin', 'arm64'), '@seqra/opentaint-darwin-arm64');
  assert.strictEqual(platformPackage('win32', 'x64'), '@seqra/opentaint-win32-x64');
  assert.strictEqual(platformPackage('win32', 'arm64'), '@seqra/opentaint-win32-arm64');
});

test('platformPackage returns undefined for unsupported combos', () => {
  assert.strictEqual(platformPackage('freebsd', 'x64'), undefined);
  assert.strictEqual(platformPackage('linux', 'ppc64'), undefined);
});

test('resolveBinary joins the package dir with the unix binary name', () => {
  const fakeResolve = (id) => {
    assert.strictEqual(id, '@seqra/opentaint-linux-x64/package.json');
    return '/somewhere/node_modules/@seqra/opentaint-linux-x64/package.json';
  };
  const bin = resolveBinary('linux', 'x64', fakeResolve);
  assert.strictEqual(bin, path.join('/somewhere/node_modules/@seqra/opentaint-linux-x64', 'opentaint'));
});

test('resolveBinary uses opentaint.exe on win32', () => {
  const fakeResolve = () => 'C:\\\\node_modules\\\\@seqra\\\\opentaint-win32-x64\\\\package.json';
  const bin = resolveBinary('win32', 'x64', fakeResolve);
  assert.ok(bin.endsWith('opentaint.exe'), `expected .exe suffix, got ${bin}`);
});

test('resolveBinary throws a clear error for unsupported platforms', () => {
  assert.throws(
    () => resolveBinary('freebsd', 'x64', () => 'unused'),
    /does not ship a prebuilt binary for freebsd\/x64/
  );
});

test('resolveBinary throws when the platform package is not installed', () => {
  const failingResolve = () => { throw new Error('Cannot find module'); };
  assert.throws(
    () => resolveBinary('linux', 'x64', failingResolve),
    /@seqra\/opentaint-linux-x64 is not installed/
  );
});

test('signalExitCode returns 128 + signal number, or 1 when unknown', () => {
  const os = require('node:os');
  assert.strictEqual(signalExitCode('SIGTERM'), 128 + os.constants.signals.SIGTERM);
  assert.strictEqual(signalExitCode('NOPE'), 1);
});

test('run passes argv through and returns the child status', () => {
  let captured;
  const spawn = (bin, argv, opts) => {
    captured = { bin, argv, opts };
    return { status: 0 };
  };
  const code = run(['scan', '--help'], {
    platform: 'linux',
    arch: 'x64',
    resolve: () => '/n/@seqra/opentaint-linux-x64/package.json',
    spawn,
  });
  assert.strictEqual(code, 0);
  assert.deepStrictEqual(captured.argv, ['scan', '--help']);
  assert.deepStrictEqual(captured.opts, { stdio: 'inherit' });
  assert.ok(captured.bin.endsWith(path.join('opentaint-linux-x64', 'opentaint')));
});

test('run propagates a non-zero child exit code', () => {
  const code = run([], {
    platform: 'linux',
    arch: 'x64',
    resolve: () => '/n/@seqra/opentaint-linux-x64/package.json',
    spawn: () => ({ status: 3 }),
  });
  assert.strictEqual(code, 3);
});

test('run maps signal termination to 128 + signal', () => {
  const os = require('node:os');
  const code = run([], {
    platform: 'linux',
    arch: 'x64',
    resolve: () => '/n/@seqra/opentaint-linux-x64/package.json',
    spawn: () => ({ status: null, signal: 'SIGTERM' }),
  });
  assert.strictEqual(code, 128 + os.constants.signals.SIGTERM);
});

test('run writes an error and returns 1 when resolution fails', () => {
  let err = '';
  const code = run([], {
    platform: 'linux',
    arch: 'x64',
    resolve: () => { throw new Error('missing'); },
    spawn: () => { throw new Error('should not spawn'); },
    stderr: { write: (s) => { err += s; } },
  });
  assert.strictEqual(code, 1);
  assert.match(err, /opentaint: .*not installed/);
});
