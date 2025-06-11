# UCICore

*A formal Lean 4 skeleton for the **Universal Classification Impossibility** (UCI) framework and its companion existence‑duality program.*

---

## 1  Purpose

UCICore supplies the minimal Lean machinery needed to instantiate the UCI template—the diagonal argument showing that **no finite‑information classifier can perfectly decide membership in an exceptional set**—together with hooks for the dual "bounded‑continuous" existence principle.  It is designed to be imported by concrete impossibility proofs without pulling in heavyweight dependencies.

### 1.1  Theoretical backdrop

> **Spatial Necessity: Mapping the Architecture of Mathematical Constraint**
> *Through systematic abstraction of classical theorems, we discover that mathematics is governed by two fundamental laws of necessity.*
> **Part I** proves that fourteen major impossibility theorems across logic, computation, and systems theory are instances of a single result—the **Universal Classification Impossibility**: any system attempting complete classification fails when confronted with an object that contradicts its own classification.
> **Part II** reveals that core existence theorems share an identical structure—the **Universal Existence Principle**: any bounded continuous system must contain objects that cannot escape their essential properties due to topological constraints.
> **Part III** unifies these two laws under the **Imagination Principle**, which asserts that the boundary of logical possibility coincides exactly with the boundary of coherent conception. From this, we derive the first complete theory of what mathematics can and cannot prove.
> We demonstrate a **100 % match rate (14/14)** for the impossibility template across logic, computation, social choice, mechanism design, distributed systems, and optimization, with perfect categorical separation from physical limitations and existence theorems.
> The existence template matches **83 % (5/6)**, with boundaries marked by choice‑dependent constructions.
> Together, these findings reveal the fundamental architecture underlying all mathematical reasoning about necessity, unifying over a century of seemingly disparate results under two universal principles—now shown to be dual manifestations of a single constraint on rational thought.

---

## 2  Repository layout

```
UCICore/
├─ UCICore.lean      -- generic UCI engine (classifier ⟶ contradiction)
└─ README.md         -- this file
```

UCICore depends only on:

* **mathlib‑4** (Lean 4.20.0 or newer)
* **Godelnumbering** – total numeric decoder + transport
* **Kleene2**        – Gödel‑generic second recursion theorem

---

## 3  Quick start

```bash
lake init UCICore git https://github.com/<you>/UCICore.git
cd UCICore
lake update   # fetch deps & generate manifest
lake build
```

Then open `UCICore.lean` in VS Code or fire up a `lake repl`:

```lean
import UCICore
open Kleene.UCI

-- toy classifier on ℕ: evenness
def evenCls : Classifiers ℕ := ⟨fun n => decide (n % 2 = 0)⟩

-- build the six hypotheses (trivial for identity numbering)…
-- uci evenCls _ _ _ _ _   -- ⟹ False
```

