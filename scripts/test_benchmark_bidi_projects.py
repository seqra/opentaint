import unittest
from unittest.mock import patch
import argparse
from pathlib import Path
from types import SimpleNamespace
import os

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

    def test_iteration_profile_is_eligible_only_in_requested_active_run(self):
        windows = benchmark_bidi_projects.iteration_profile_windows
        self.assertEqual([('run-4-normal', 123.0, 60)], windows([4, 6, 8], 4, True, {4: 123.0}))
        self.assertEqual([], windows([4, 6, 8], 4, False, {4: 123.0}))
        self.assertEqual([], windows([4, 6, 8], 3, True, {3: 123.0}))
        self.assertEqual([], windows([4], 4, True, {}))

    def test_invalid_iteration_targets_fail_before_starting_analysis(self):
        for value in ['0', '-1', 'run-4', '4.0', '4;true']:
            with self.assertRaises(argparse.ArgumentTypeError):
                benchmark_bidi_projects.positive_iteration(value)
        self.assertEqual(4, benchmark_bidi_projects.positive_iteration('4'))

    def test_phase_snapshot_records_external_capture_cost_and_actual_latest_run(self):
        result = SimpleNamespace(returncode=0, stdout='Recording written')
        with patch.dict(os.environ, {'JAVA_HOME': '/jdk'}), \
                patch.object(benchmark_bidi_projects.subprocess, 'run', return_value=result) as command, \
                patch.object(benchmark_bidi_projects.time, 'monotonic', side_effect=[10., 10.25]):
            receipt = benchmark_bidi_projects.dump_jfr(123, Path('/capture'), 'run-7-end', 100., 8)
        self.assertEqual(8, receipt['latest_run'], 'The next engine can already be active at capture')
        self.assertEqual(.25, receipt['capture_wall_seconds'])
        self.assertEqual(0, receipt['returncode'])
        self.assertEqual(['/jdk/bin/jcmd', '123', 'JFR.dump', 'filename=/capture/run-7-end.jfr'],
                         command.call_args.args[0])


class CaptureControlLinesTest(unittest.TestCase):
    def parser(self):
        return benchmark_bidi_projects.CaptureControlLines()

    def test_end_marker_survives_a_large_body_dump_in_the_same_poll(self):
        reader = self.parser()
        end = '18:00:00 |I| IterationDriver - BIDI_RUN_END run=1 status=COMPLETE engineTime=2s'
        body = '18:00:00 |I| IterationDriver - BIDI_BODY_WORK_METHOD ' + 'x' * (1024 * 1024)
        data = end + '\n' + body + '\n'
        observed = []
        for offset in range(0, len(data), 65536):
            observed.extend(reader.feed(data[offset:offset + 65536]))
            self.assertLessEqual(len(reader.pending), reader.line_limit)
        self.assertEqual(['BIDI_RUN_END run=1 status=COMPLETE engineTime=2s'], observed)
        self.assertEqual([], list(reader.feed('')), 'Previously consumed markers are not replayed')

    def test_marker_and_run_number_split_across_polls_wait_for_complete_line(self):
        reader = self.parser()
        self.assertEqual([], list(reader.feed('18:00:00 |I| IterationDriver - BIDI_RUN_STA')))
        self.assertEqual([], list(reader.feed('RT run=1')))
        self.assertEqual([], list(reader.feed('2 direction=BACKWARD limit=11')))
        self.assertEqual(['BIDI_RUN_START run=12 direction=BACKWARD limit=11'], list(reader.feed('\n')))

    def test_oversized_unrelated_line_is_discarded_until_newline_then_markers_resume(self):
        reader = self.parser()
        self.assertEqual([], list(reader.feed('BIDI_BODY_WORK_METHOD ' + 'x' * 10000)))
        self.assertEqual('', reader.pending)
        observed = list(reader.feed('BIDI_RUN_END run=99 status=COMPLETE\n'
                                    'BIDI_RUN_END run=2 status=COMPLETE engineTime=3s\n'))
        self.assertEqual(['BIDI_RUN_END run=2 status=COMPLETE engineTime=3s'], observed)
        self.assertEqual('', reader.pending)

    def test_small_diagnostic_message_cannot_supply_a_nested_marker(self):
        reader = self.parser()
        data = ('18:00:00 |I| IterationDriver - BIDI_BODY_WORK_METHOD method='
                'java.lang.OutOfMemoryError#x - BIDI_RUN_END run=99 status=OOM\n'
                '18:00:00 |I| IterationDriver - BIDI_RUN_START run=3 direction=FORWARD limit=2\n')
        self.assertEqual(['BIDI_RUN_START run=3 direction=FORWARD limit=2'], list(reader.feed(data)))

    def test_ordered_phase_and_run_controls_survive_every_character_boundary(self):
        reader = self.parser()
        expected = ['Start IFDS analysis', 'BIDI_RUN_START run=1 direction=FORWARD limit=1',
                    'BIDI_RUN_END run=1 status=COMPLETE engineTime=1s',
                    'BIDI_RUN_START run=2 direction=BACKWARD limit=1',
                    'BIDI_ANALYSIS_END run=2 status=TIMEOUT reason=ABNORMAL elapsed=2s',
                    'Finish IFDS analysis']
        observed = []
        for char in '\n'.join(expected) + '\n':
            observed.extend(reader.feed(char))
        self.assertEqual(expected, observed)

    def test_line_limit_is_inclusive_and_does_not_leak_an_oversized_prefix(self):
        reader = self.parser()
        marker = 'BIDI_RUN_END run=8 status=COMPLETE '
        at_limit = marker + 'x' * (reader.line_limit - len(marker))
        self.assertEqual([at_limit], list(reader.feed(at_limit + '\n')))
        self.assertEqual([], list(reader.feed(at_limit + 'x\n')))


if __name__ == '__main__':
    unittest.main()
