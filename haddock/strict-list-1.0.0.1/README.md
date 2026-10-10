# strict-list

[![Hackage](https://img.shields.io/hackage/v/strict-list.svg)](https://hackage.haskell.org/package/strict-list)
[![Continuous Haddock](https://img.shields.io/badge/haddock-master-blue)](https://nikita-volkov.github.io/strict-list/)

Strict linked lists for Haskell, with stack-safe operations and reversed-order helpers for efficient intermediate work.

## Example

```haskell
{-# LANGUAGE OverloadedLists #-}

import StrictList

numbers :: StrictList Int
numbers = [1, 2, 3]
```
