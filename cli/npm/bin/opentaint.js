#!/usr/bin/env node
'use strict';

const path = require('node:path');
const os = require('node:os');
const { spawnSync } = require('node:child_process');

const SCOPE = '@seqra';

const SUPPORTED_PLATFORMS = new Set([
  'linux x64',
  'linux arm64',
  'darwin x64',
  'darwin arm64',
  'win32 x64',
  'win32 arm64',
]);

function platformPackage(platform, arch) {
  if (!SUPPORTED_PLATFORMS.has(`${platform} ${arch}`)) {
    return undefined;
  }
  return `${SCOPE}/opentaint-${platform}-${arch}`;
}

function resolveBinary(platform, arch, resolve) {
  resolve = resolve || ((id) => require.resolve(id));
  const pkg = platformPackage(platform, arch);
  if (!pkg) {
    throw new Error(
      `opentaint does not ship a prebuilt binary for ${platform}/${arch}. ` +
      `Supported platforms: ${Array.from(SUPPORTED_PLATFORMS).map((p) => p.replace(' ', '/')).join(', ')}.`
    );
  }
  const binName = platform === 'win32' ? 'opentaint.exe' : 'opentaint';
  let pkgJsonPath;
  try {
    pkgJsonPath = resolve(`${pkg}/package.json`);
  } catch (_e) {
    throw new Error(
      `The platform package ${pkg} is not installed. This usually means ` +
      `optional dependencies were skipped (e.g. "npm install --no-optional" ` +
      `or "--omit=optional"). Reinstall opentaint without omitting optional dependencies.`
    );
  }
  return path.join(path.dirname(pkgJsonPath), binName);
}

function signalExitCode(signal) {
  const num = os.constants.signals[signal];
  return num ? 128 + num : 1;
}

function run(argv, opts) {
  opts = opts || {};
  const platform = opts.platform || process.platform;
  const arch = opts.arch || process.arch;
  const spawn = opts.spawn || spawnSync;
  const stderr = opts.stderr || process.stderr;

  let binary;
  try {
    binary = resolveBinary(platform, arch, opts.resolve);
  } catch (e) {
    stderr.write(`opentaint: ${e.message}\n`);
    return 1;
  }

  const result = spawn(binary, argv, { stdio: 'inherit' });
  if (result.error) {
    stderr.write(`opentaint: failed to launch ${binary}: ${result.error.message}\n`);
    return 1;
  }
  if (typeof result.status === 'number') {
    return result.status;
  }
  if (result.signal) {
    return signalExitCode(result.signal);
  }
  return 1;
}

module.exports = { SCOPE, SUPPORTED_PLATFORMS, platformPackage, resolveBinary, signalExitCode, run };

if (require.main === module) {
  process.exit(run(process.argv.slice(2)));
}
