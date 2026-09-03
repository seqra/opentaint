'use strict';

const { createTransform, TYPES } = require('../release-notes-transform.cjs');
const {
  RELEASE_PARSER_OPTIONS,
  createReleaseRules,
} = require('../.github/scripts/scope-contract.cjs');

module.exports = {
  tagFormat: 'github/v${version}',
  branches: [
    'main',
    {
      name: 'release*',
      prerelease: true,
    },
  ],
  ci: false,
  plugins: [
    [
      '@semantic-release/commit-analyzer',
      {
        preset: 'conventionalcommits',
        parserOpts: RELEASE_PARSER_OPTIONS,
        releaseRules: createReleaseRules('github'),
      },
    ],
    [
      '@semantic-release/release-notes-generator',
      {
        preset: 'conventionalcommits',
        parserOpts: RELEASE_PARSER_OPTIONS,
        presetConfig: { types: TYPES },
        writerOpts: {
          transform: createTransform(['github']),
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
        draftRelease: true,
        assets: [],
      },
    ],
    [
      '@semantic-release/exec',
      {
        prepareCmd: 'echo v${nextRelease.version} > release_version.txt',
      },
    ],
  ],
};
