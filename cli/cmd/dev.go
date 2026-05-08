package cmd

import (
	"github.com/spf13/cobra"
)

// devCmd represents the dev command group
var devCmd = &cobra.Command{
	Use:   "dev",
	Short: "Create and debug rules (experimental)",
	Long:  `This command provides utilities for rule authoring and debugging (experimental)`,
}

func init() {
	rootCmd.AddCommand(devCmd)
}
