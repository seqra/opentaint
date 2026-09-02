'use strict';

const { createTransform, TYPES } = require('../release-notes-transform.cjs');
const {
  RELEASE_PARSER_OPTIONS,
  createReleaseRules,
} = require('../.github/scripts/scope-contract.cjs');

module.exports = {
  tagFormat: 'rules/v${version}',
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
        releaseRules: createReleaseRules('rules'),
      },
    ],
    [
      '@semantic-release/release-notes-generator',
      {
        preset: 'conventionalcommits',
        parserOpts: RELEASE_PARSER_OPTIONS,
        presetConfig: { types: TYPES },
        writerOpts: {
          transform: createTransform(['rules']),
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
        assets: [
          {
            path: '../opentaint-rules.tar.gz',
            label: 'opentaint-rules.tar.gz',
          },
        ],
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
