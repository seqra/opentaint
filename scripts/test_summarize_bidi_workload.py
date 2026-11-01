import io
import json
import unittest

from summarize_bidi_workload import add, counters, events, finish, scope


class WorkloadProfileTest(unittest.TestCase):
    def test_disjoint_scope_precedence_keeps_callbacks_out_of_call_totals(self):
        direct = 'org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process'
        replay = 'org.opentaint.dataflow.bidi.engine.PersistedSummaryReplayKt.replayPersistedSummaries'
        delivery = 'org.opentaint.dataflow.bidi.engine.SubscriptionManager.onDelivery'
        c5 = 'org.opentaint.dataflow.bidi.store.DemandStore.intersect'
        self.assertEqual('direct_call', scope([direct]))
        self.assertEqual('saved_replay', scope([direct, replay]))
        self.assertEqual('current_delivery', scope([delivery, direct, replay]))
        self.assertEqual('c5_restriction', scope([c5, delivery, direct, replay]))
        self.assertEqual('other', scope(['java.lang.String.valueOf']))

    def test_stream_reader_handles_event_larger_than_buffer_and_empty_array(self):
        values = [{'type': 'first', 'values': {'payload': 'x' * 70000}},
                  {'type': 'second', 'values': {}}]
        self.assertEqual(values, list(events(io.StringIO(json.dumps({'recording': {'events': values}})))))
        self.assertEqual([], list(events(io.StringIO('{"recording":{"events":[]}}'))))
        with self.assertRaises(ValueError):
            list(events(io.StringIO('{"recording":{"events":[{"type":"broken"')))

    def event(self, kind, frame_names, **values):
        frames = []
        for name in frame_names:
            cls, method = name.rsplit('.', 1)
            frames.append({'method': {'type': {'name': cls}, 'name': method}})
        return {'type': kind, 'values': dict(stackTrace={'frames': frames}, **values)}

    def test_scope_counts_partition_samples_and_allocation_weights(self):
        data = counters()
        direct = 'org.opentaint.dataflow.bidi.engine.RunMethodCallServices.process'
        for _ in range(3):
            add(data, self.event('jdk.ExecutionSample', [direct, direct]))
        add(data, self.event('jdk.ExecutionSample', ['java.lang.String.valueOf']))
        add(data, self.event('jdk.ObjectAllocationSample', [direct], weight=17, objectClass={'name': 'Node'}))
        add(data, self.event('jdk.ObjectAllocationSample', [], weight=23, objectClass={'name': 'Other'}))
        result = finish(data)
        self.assertEqual(4, sum(row['count'] for row in result['disjoint_scopes']))
        self.assertEqual(40, sum(row['count'] for row in result['allocation_disjoint_scopes']))
        self.assertEqual(3, result['inclusive'][0]['count'])
        self.assertEqual(1, len(result['bounded_example_stacks']['direct_call']))


if __name__ == '__main__':
    unittest.main()
