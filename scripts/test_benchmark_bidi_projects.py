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
            selected.append((args.run1_mark_mode, args.field_limit_schedule, args.heap_memory))
            raise Parsed()

        with patch.object(argparse.ArgumentParser, 'parse_args', new=capture):
            with self.assertRaises(Parsed):
                benchmark_bidi_projects.main()
        self.assertEqual([('FULL', 'REPEAT_RUN1', None)], selected)

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

    def configurations(self, *extra):
        parse = argparse.ArgumentParser.parse_args
        configs = {}

        def selected(parser):
            return parse(parser, ['--main', '/tmp/main', '--current', '/tmp/current',
                                  '--test', '/tmp/test', '--output', '/tmp/output',
                                  '--sides', 'bidi', *extra])

        def capture(args, project, side, config):
            self.assertEqual('bidi', side)
            self.assertEqual('REPEAT_RUN1', args.field_limit_schedule)
            configs[project] = dict(config)

        with patch.object(argparse.ArgumentParser, 'parse_args', new=selected), \
                patch.object(benchmark_bidi_projects, 'run', new=capture):
            benchmark_bidi_projects.main()
        return configs

    def test_16g_override_keeps_models_timeouts_and_original_defaults(self):
        defaults = self.configurations()
        large = self.configurations('--heap-memory', '16g')
        self.assertEqual({'OWASP', 'conductor', 'thingsboard', 'Stirling-PDF'}, set(large))
        self.assertEqual({'OWASP': '8g', 'conductor': '8g', 'thingsboard': '12g', 'Stirling-PDF': '8g'},
                         {key: value['memory'] for key, value in defaults.items()})
        for name, config in large.items():
            self.assertEqual('16g', config['memory'])
            self.assertEqual({key: value for key, value in defaults[name].items() if key != 'memory'},
                             {key: value for key, value in config.items() if key != 'memory'})
        before = analyzer_jvm_args(self.options('FULL'), Path('/tmp/heap'), 'bidi', '8g')
        after = analyzer_jvm_args(self.options('FULL'), Path('/tmp/heap'), 'bidi', '16g')
        self.assertEqual([x for x in before if not x.startswith('-Xmx')],
                         [x for x in after if not x.startswith('-Xmx')])
        self.assertIn('-Xmx16g', after)

    def test_invalid_heap_sizes_fail_before_starting_analysis(self):
        for value in ['0g', '-1g', '16', '16gb', '1.5g', '16g -Xmx32g']:
            with self.assertRaises(argparse.ArgumentTypeError):
                benchmark_bidi_projects.heap_memory(value)
        self.assertEqual('16g', benchmark_bidi_projects.heap_memory('16G'))


if __name__ == '__main__':
    unittest.main()
