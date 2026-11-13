package cmd

import "testing"

func TestTestCompileCommand(t *testing.T) {
	tests := []struct {
		outputDir, side, want string
	}{
		{".opentaint/test-projects/my-rule", "<side>",
			"opentaint compile .opentaint/test-projects/my-rule/<side> -o .opentaint/test-compiled/my-rule/<side>"},
		{".opentaint/test-projects/my-rule", "sinks",
			"opentaint compile .opentaint/test-projects/my-rule/sinks -o .opentaint/test-compiled/my-rule/sinks"},
		{".opentaint/test-projects/my-model", "",
			"opentaint compile .opentaint/test-projects/my-model -o .opentaint/test-compiled/my-model"},
		{"./.opentaint/test-projects/my-model/", "",
			"opentaint compile ./.opentaint/test-projects/my-model -o ./.opentaint/test-compiled/my-model"},
		{"/home/user/app/.opentaint/test-projects/my-rule", "sources",
			"opentaint compile /home/user/app/.opentaint/test-projects/my-rule/sources -o /home/user/app/.opentaint/test-compiled/my-rule/sources"},
		{"tests/my rule", "<side>", "opentaint compile 'tests/my rule'/<side>"},
	}
	for _, tc := range tests {
		if got := testCompileCommand(tc.outputDir, tc.side); got != tc.want {
			t.Errorf("testCompileCommand(%q, %q) = %q, want %q", tc.outputDir, tc.side, got, tc.want)
		}
	}
}
