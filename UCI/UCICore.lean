/-
# Universal Classification Impossibility (UCI) engine

This module bundles the generic diagonal‑argument that shows **no computable
finite‑information classifier can perfectly separate an “exceptional” subset**
of a Gödel‑coded universe.  It is the formal core underlying the impossibility
claims in the accompanying papers *Collatz at the House Edge* and *Spatial
Necessity*.

The file is intentionally self‑contained – the only imports beyond mathlib are
our helper libraries **Godelnumbering** (total `numToCode` + transport) and
**Kleene2** (Gödel‑generic second recursion theorem).

## Module layout

| Section | Purpose |
|---------|---------|
| **Classifier API**     | Defines a *bundled* Boolean predicate `Classifier D`. |
| **Two constant codes** | Convenience constants `code0/code1` used as Boolean tags. |
| **`uci` theorem**      | The engine: given a computable classifier and mild extensionality assumptions, derives `False`. |

Because the final contradiction still relies on domain‑specific facts
(`hCode0`, `hCode1`), this file stops one step short of a *fully* generic UCI
lemma – but all the computability plumbing is in place.

*No `sorry`s, no external axioms.*


-/

import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec
import Mathlib.Data.Bool.Basic
import Kleene2.KleeneFix            -- kleene_fix
import Godelnumbering.Transport

open Classical
open Godel
open Nat.Partrec Code
open Primrec
open Kleene       -- for `kleene_fix`


namespace Kleene.UCI
namespace Classifier

/-! ## Classifier bundle -/

/-! A *bundled* Boolean predicate on `D`.  Bundling keeps the classifier’s
    computability proof (`hC`) separate from its definition. -/
/-- Bundled Boolean predicate on a domain `D`. -/
structure Classifiers (D : Type) where
  /-- The underlying Boolean predicate. -/
  C : D → Bool

variable {D : Type} [Numbering D] [Primcodable D]

/-! ## Constant codes used as Boolean tags  -/

private def code0 : Code := Code.const 0   -- ⟨∅⟩
private def code1 : Code := Code.const 1   -- ⟨true⟩

@[simp] lemma eval_code0 (x : ℕ) : code0.eval x = pure 0 := by
  simp [code0]

@[simp] lemma eval_code1 (x : ℕ) : code1.eval x = pure 1 := by
  simp [code1]

/-! ## Numeral helper for `Bool` (may be useful elsewhere) -/
private def b2n : Bool → ℕ | true => 1 | false => 0
@[simp] lemma b2n_true  : b2n true  = 1 := rfl
@[simp] lemma b2n_false : b2n false = 0 := rfl

/-! ## Universal Classification Impossibility  -/

/-- **`uci`** — core diagonal argument.

Inputs
* `Φ`   – computable classifier bundled as `Classifier D`.
* `hC`   – proof that `Φ.C` is `Computable`.
* `hDec` – computable decoding map (usually `Computable.id` for `ℕ`).
* `hExt` – *extensionality*: classifiers respect code‑level equality.
* `hCode0 / hCode1` – the classifier’s behaviour on the two constant codes.

Outputs
* `False`.  (Hence such a simultaneously computable & extensional classifier
  cannot exist with both `hCode0` and `hCode1`.)

The proof follows the standard script:
1.  Build a computable *bit* function that queries the classifier on the
    decoded form of a code.
2.  Turn that bit into a *selector* that chooses `code0` or `code1`.
3.  Define `f : Code → Code` using the selector; obtain a Kleene fixed point
    `c₀` for `f`.
4.  Evaluate both sides at input `0` to relate the classifier’s bit to the
    constant codes.
5.  Use `hExt` to transfer the classifier value across the extensional
    equality, split on the Boolean, and contradict `hCode0` / `hCode1`.

This is exactly the plumbing needed for the UCI template; domain‑specific
projects supply concrete `Φ`, `hCode0`, `hCode1` to obtain their own
impossibility corollaries. -/
lemma uci
    (Φ    : Classifiers D)
    (hC   : Computable Φ.C)
    (hDec : Computable (fun n : ℕ => (Numbering.decode n : D)))
    (hExt : ∀ {c₁ c₂ : Code},                     -- extensionality
            c₁.eval = c₂.eval →
            Φ.C (Numbering.decode (Encodable.encode c₁)) =
            Φ.C (Numbering.decode (Encodable.encode c₂)))
    (hCode0 : Φ.C (Numbering.decode (Encodable.encode code0)) = false)
    (hCode1 : Φ.C (Numbering.decode (Encodable.encode code1)) = true) :
    False := by
  classical

  ------------------------------------------------------------------
  -- 1 ▸ `bit` : Code → Bool   (asks Φ about the decoded code)
  ------------------------------------------------------------------
  have hBit : Computable (fun c : Code => Φ.C (Numbering.decode (Encodable.encode c))) := by
    have hEnc  : Computable (fun c : Code => Encodable.encode c) := Computable.encode
    have hDecE : Computable (fun c : Code => (Numbering.decode (Encodable.encode c) : D)) :=
      hDec.comp hEnc
    exact hC.comp hDecE

  ------------------------------------------------------------------
  -- 2 ▸ `selector` : Bool → Code   (maps the bit to one of two constants)
  ------------------------------------------------------------------
  have hSelPrim : Primrec (fun b : Bool => if b then code0 else code1) := by
    -- `Primrec.ite` expects a `Prop` predicate; supply `b = true`.
    have hPred : PrimrecPred (fun b : Bool => b = true) := by
      dsimp [PrimrecPred]
      simpa using (Primrec.id : Primrec (fun b : Bool => b))
    simpa using
      Primrec.ite hPred (Primrec.const code0) (Primrec.const code1)

  have hSel : Computable (fun b : Bool => if b then code0 else code1) :=
    hSelPrim.to_comp

  ------------------------------------------------------------------
  -- 3 ▸ Transformer `f : Code → Code`
  ------------------------------------------------------------------
  let f : Code → Code := fun c =>
    if Φ.C (Numbering.decode (Encodable.encode c)) then code0 else code1

  have hf : Computable f := by
    simpa [f] using hSel.comp hBit

  ------------------------------------------------------------------
  -- 4 ▸ Kleene fixed point   c₀.eval = (f c₀).eval
  ------------------------------------------------------------------
  rcases kleene_fix hf with ⟨c₀, hc⟩
  let d : D := Numbering.decode (Encodable.encode c₀)

  ------------------------------------------------------------------
  -- 5 ▸ Transport classifier values and split on Φ.C d
  ------------------------------------------------------------------
  -- 5·1  Use extensionality to move Φ across the equality hc.
  have hΦ_eq : Φ.C d =
      Φ.C (Numbering.decode (Encodable.encode (f c₀))) := by
    dsimp [d] at *
    exact hExt hc

  -- 5·2  Case split on `b := Φ.C d`.
  have : False := by
    cases hCd : Φ.C d with
    | false =>
        have hf' : f c₀ = code1 := by simp [f, d, hCd]
        have hEq' : (false : Bool) =
            Φ.C (Numbering.decode (Encodable.encode code1)) := by
          simpa [hCd, hf'] using hΦ_eq
        have hContr : (false : Bool) = true := by
          simpa [hCode1] using hEq'
        cases hContr
    | true =>
        have hf' : f c₀ = code0 := by simp [f, d, hCd]
        have hEq' : (true : Bool) =
            Φ.C (Numbering.decode (Encodable.encode code0)) := by
          simpa [hCd, hf'] using hΦ_eq
        have hContr : (true : Bool) = false := by
          simpa [hCode0] using hEq'
        cases hContr
  exact this

end Classifier
end Kleene.UCI

#lint
