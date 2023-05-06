# EH-Digger
Underneath the Iceberg: Understanding and Mining the Underlying Errors of Error-Handling Code

---

## Introduction
EH-Digger is a bug detection tool for error-handling bugs. Manually constructing templates or error specifications requires much human effort and is difficult to accommodate the software evolution, while existing learning-based approaches are hard to learn real reasons of the error-handling code in many cases. The main reason of this limitation is that existing approaches only learn API calls near error-handling code snippets, instead of trying to understanding the underlying errors handled by these code snippets. Accordingly, we design EH-Digger, an automated tool to detect error-handling bugs by mining handling patterns of underlying errors.


## Usage

### Dependency

- Tree-sitter 0.20.0
- Prefixspan 0.5.2
- numpy 1.12.1

### Envirment Setup

- Download grammars for tree-sitter.

```
git clone https://github.com/tree-sitter/tree-sitter-c
git clone https://github.com/tree-sitter/tree-sitter-cpp
```

- Add the paths to these grammars to TreesitterInit.

```
Language.build_library(
  # Store the library in the `build` directory
  'build/my-languages.so',
  # Include one or more languages
  [
  Path1,
  Path2
  ]
)
```

- Run TreesitterInit.py.

```
sudo ./TreesitterInit.py
```

- EH-Digger requires the project to be structured as follow.

```
Working Dir
|
|----Test
|        |----project1
|        |----project2
|
|----TestResult
|        |----result1
|        |----return2
```

- Add the path of the Working Dir to Config.

```
workingDir = Working Dir
```

- Add the project name and corresponding error log patterns.

```
pInfoList = [[ProjectName, [Error Log Pattern],[Error Log Pattern],...]]
```

### Run EH-Digger

```
sudo ./EH-Digger.py
```

### Check Result

```
cat Working Dir/Test/ProjectName/Pattern
cat Working Dir/Test/ProjectName/Finded Bug
```
