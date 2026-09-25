import Lake
open Lake DSL

package «markset-scan» where

@[default_target]
lean_lib MarkScan where

lean_exe «markset-oracle» where
  root := `Oracle
