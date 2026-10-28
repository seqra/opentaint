import unittest
from unittest.mock import patch
import argparse
from pathlib import Path
from types import SimpleNamespace

from benchmark_bidi_projects import analyzer_jvm_args
import benchmark_bidi_projects


class AnalyzerConfigurationTest(unittest.TestCase):
    def test_absent_mode_option_selects_full_before_starting_any_measurement(self):
        class Parsed(Exception):
            pass

        parse = argparse.ArgumentParser.parse_args
        selected = []

        def capture(parser):
            args = parse(parser, ['--main', '/tmp/main', '--current', '/tmp/current',
                                  '--test', '/tmp/test', '--output', '/tmp/output'])
            selected.append((args.run1_mark_mode, args.field_limit_schedule))
            raise Parsed()

        with patch.object(argparse.ArgumentParser, 'parse_args', new=capture):
            with self.assertRaises(Parsed):
                benchmark_bidi_projects.main()
        self.assertEqual([('FULL', 'REPEAT_RUN1')], selected)

    def options(self, mode):
        return SimpleNamespace(run1_mark_mode=mode, heap_snapshots=True,
                               form_statistics=True, optimization_statistics=True)

    def test_paired_modes_change_only_the_selected_property(self):
        path = Path('/tmp/paired-run')
        group = analyzer_jvm_args(self.options('GROUP'), path, 'bidi', '12g')
        full = analyzer_jvm_args(self.options('FULL'), path, 'bidi', '12g')
        self.assertEqual([x for x in group if 'run1MarkMode=' not in x],
                         [x for x in full if 'run1MarkMode=' not in x])
        self.assertIn('-Dopentaint.bidi.run1MarkMode=GROUP', group)
        self.assertIn('-Dopentaint.bidi.run1MarkMode=FULL', full)
        self.assertIn('-Dopentaint.bidi.disableRun1Statics=false', full)
        self.assertIn('-Xmx12g', full)

    def test_main_has_no_candidate_flags_and_keeps_the_same_capture_policy(self):
        path = Path('/tmp/main-run')
        values = analyzer_jvm_args(self.options('FULL'), path, 'main', '8g')
        self.assertFalse(any('bidi.' in x for x in values))
        self.assertIn('-Dopentaint.memorySnapshotDir=/tmp/main-run', values)
        self.assertTrue(any(x.startswith('-Xlog:gc*:') for x in values))

    def test_schedule_experiment_changes_only_schedule_in_analyzer_jvm(self):
        options = self.options('FULL')
        options.field_limit_schedule = 'REPEAT_RUN1'
        current = analyzer_jvm_args(options, Path('/tmp/schedule'), 'bidi', '8g')
        options.field_limit_schedule = 'RUN_INDEX'
        experiment = analyzer_jvm_args(options, Path('/tmp/schedule'), 'bidi', '8g')
        self.assertEqual([x for x in current if 'fieldLimitSchedule=' not in x],
                         [x for x in experiment if 'fieldLimitSchedule=' not in x])
        self.assertIn('-Dopentaint.bidi.fieldLimitSchedule=REPEAT_RUN1', current)
        self.assertIn('-Dopentaint.bidi.fieldLimitSchedule=RUN_INDEX', experiment)


if __name__ == '__main__':
    unittest.main()
