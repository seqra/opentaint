'use strict';

const { createTransform, TYPES } = require('../release-notes-transform.cjs');

module.exports = {
  tagFormat: 'models/v${version}',
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
        releaseRules: [
          { scope: 'model', breaking: true, release: 'major' },
          { scope: 'model', type: 'feat', release: 'minor' },
          { scope: 'model', type: 'fix', release: 'patch' },
          { scope: 'model', type: 'refactor', release: 'patch' },
          { scope: 'model', type: 'revert', release: 'patch' },
          { scope: '!(model)', release: false },
        ],
      },
    ],
    [
      '@semantic-release/release-notes-generator',
      {
        preset: 'conventionalcommits',
        presetConfig: { types: TYPES },
        writerOpts: {
          transform: createTransform(['model']),
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
            path: '../opentaint-models.tar.gz',
            label: 'opentaint-models.tar.gz',
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
