'use strict';

const { createTransform, TYPES } = require('../release-notes-transform.cjs');
const {
  RELEASE_PARSER_OPTIONS,
  createReleaseRules,
} = require('../.github/scripts/scope-contract.cjs');

module.exports = {
  branches: [
    'main',
    {
      name: 'release/**',
      prerelease: "${name.split('/').slice(0, 2).join('-').toLowerCase()}",
    },
  ],
  ci: false,
  plugins: [
    [
      '@semantic-release/commit-analyzer',
      {
        preset: 'conventionalcommits',
        parserOpts: RELEASE_PARSER_OPTIONS,
        releaseRules: createReleaseRules('cli'),
      },
    ],
    [
      '@semantic-release/release-notes-generator',
      {
        preset: 'conventionalcommits',
        parserOpts: RELEASE_PARSER_OPTIONS,
        presetConfig: { types: TYPES },
        writerOpts: {
          transform: createTransform(['cli', 'rules', 'analyzer', 'autobuilder', 'core']),
        },
      },
    ],
    [
      '@semantic-release/github',
      {
        successComment: false,
        failTitle: false,
        labels: false,
        releasedLabels: false,
        assets: [],
      },
    ],
    [
      '@semantic-release/exec',
      {
        prepareCmd: 'echo ${nextRelease.version} > release_version.txt',
      },
    ],
  ],
};
