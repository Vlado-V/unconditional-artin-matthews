module

public import ArtinMatthews.GiantSignedGhostMemoryProduct
public import ArtinMatthews.GiantSignedGhostSimultaneous
public import ArtinMatthews.GiantSignedGhostCoordinateRestriction
public import ArtinMatthews.GiantSignedGhostSimultaneousFactorization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal simultaneous row equals the original finite coordinate word. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
universe u

private theorem giantSignedGhostProduct_word_aux (n : ℕ) :
    ∀ (B : Type u) [Fintype B] [DecidableEq B] (P : B → Finset ℕ)
      (ν : ∀ g, P g → ℝ) (_hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
      (f : GiantSignedMemoryGroups P → ℂ) (_hf : GiantSignedGhostProductExponential f)
      (gs : List B), gs.length = n → gs.Nodup → (∀ g, g ∈ gs) →
      ∀ x : GiantSignedMemoryGroups P,
        giantSignedGhostProductSimultaneousApply ν A C D f x =
          giantSignedGhostCoordinateWord ν A C D gs f x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ _ P ν hν A C D f hf gs hlen hnd hcover x
    cases gs with
    | nil =>
      let _ : IsEmpty B := ⟨fun g => by simpa using hcover g⟩
      let _ : Unique (GiantSignedGhostProductMoves x) :=
        ⟨⟨fun g => isEmptyElim g⟩, fun r => funext fun g => isEmptyElim g⟩
      have ht (r : GiantSignedGhostProductMoves x) :
          giantSignedGhostProductMoveTarget x r = x := by
        funext g
        exact isEmptyElim g
      simp [giantSignedGhostProductSimultaneousApply,
        giantSignedGhostProductMoveCoefficient, ht, giantSignedGhostCoordinateWord]
    | cons g gs =>
      have hnot : g ∉ gs := (List.nodup_cons.mp hnd).1
      have hndgs : gs.Nodup := (List.nodup_cons.mp hnd).2
      have hdis (a : B) (ha : a ∈ gs) : a ≠ g := by
        intro he
        exact hnot (he ▸ ha)
      let tail : List {h : B // h ≠ g} :=
        gs.attach.map (fun h => ⟨h.val, hdis h.val h.property⟩)
      have hmap : tail.map Subtype.val = gs := by
        simpa only [tail, List.map_map, Function.comp_def] using List.attach_map_subtype_val gs
      have htlen : tail.length = gs.length := by simp [tail]
      have htnd : tail.Nodup := List.Nodup.of_map Subtype.val (hmap.symm ▸ hndgs)
      have htcover (h : {h : B // h ≠ g}) : h ∈ tail := by
        have hh : h.val ∈ gs := by
          rcases List.mem_cons.mp (hcover h.val) with he | hm
          · exact False.elim (h.property he)
          · exact hm
        apply List.mem_map.mpr
        refine ⟨⟨h.val, hh⟩, ?_, ?_⟩
        · exact List.mem_attach gs _
        · exact Subtype.ext rfl
      have hlt : gs.length < n := by
        rw [← hlen]
        exact Nat.lt_succ_self _
      have htail (r : GiantSignedGhostMoves (x g)) :=
        ih gs.length hlt {h : B // h ≠ g} (fun h => P h)
          (fun h => ν h) (fun h p => hν h p) (fun h => A h) (fun h => C h) (fun h => D h)
          (fun y => f ((giantSignedMemorySplit P g).symm
            (giantSignedGhostMoveTarget (x g) r, y)))
          (giantSignedGhostProduct_tail_exponential f hf g (giantSignedGhostMoveTarget (x g) r))
          tail htlen htnd htcover (fun h => x h)
      obtain ⟨Cf, w, hCf, hw, hbound⟩ := hf
      calc
        _ = ∑' r : GiantSignedGhostMoves (x g),
            giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) r *
              giantSignedGhostProductSimultaneousApply
                (fun h : {h : B // h ≠ g} => ν h) (fun h => A h) (fun h => C h) (fun h => D h)
                (fun y => f ((giantSignedMemorySplit P g).symm
                  (giantSignedGhostMoveTarget (x g) r, y))) (fun h => x h) :=
          giantSignedGhostProductSimultaneous_split ν hν A C D f Cf w hCf hw hbound x g
        _ = ∑' r : GiantSignedGhostMoves (x g),
            giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) r *
              giantSignedGhostCoordinateWord ν A C D gs f
                ((giantSignedMemorySplit P g).symm
                  (giantSignedGhostMoveTarget (x g) r, fun h => x h)) := by
          apply tsum_congr
          intro r
          rw [htail r, giantSignedGhostCoordinateWord_restrict, hmap]
        _ = _ := by
          have hword := giantSignedGhostCoordinateWord_exponential ν hν A C D gs f
            ⟨Cf, w, hCf, hw, hbound⟩
          obtain ⟨Cw, v, hCw, hv, hword⟩ := hword
          let y : (h : {h : B // h ≠ g}) → GiantSignedGroupMemory (P h) := fun h => x h
          have hslice := giantSignedGhostProduct_slice_bound
            (giantSignedGhostCoordinateWord ν A C D gs f) Cw v hword g y
          have hg := giantSignedGhostMoves_tsum (ν g) (hν g) (A g) (C g) (D g)
            (fun t => giantSignedGhostCoordinateWord ν A C D gs f
              ((giantSignedMemorySplit P g).symm (t, y)))
            (Cw * v ^ (∑ h : {h : B // h ≠ g}, (y h).1)) v
            (mul_nonneg hCw (pow_nonneg hv.le _)) hv.le hslice (x g)
          change _ = giantSignedGhostGroupApply (ν g) (A g) (C g) (D g)
            (fun t => giantSignedGhostCoordinateWord ν A C D gs f
              ((giantSignedMemorySplit P g).symm (t, y))) (x g)
          exact hg

theorem giantSignedGhostProductSimultaneous_eq_coordinateWord
    {B : Type u} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemoryGroups P → ℂ) (hf : GiantSignedGhostProductExponential f)
    (gs : List B) (hnd : gs.Nodup) (hcover : ∀ g, g ∈ gs) (x : GiantSignedMemoryGroups P) :
    giantSignedGhostProductSimultaneousApply ν A C D f x =
      giantSignedGhostCoordinateWord ν A C D gs f x :=
  giantSignedGhostProduct_word_aux gs.length B P ν hν A C D f hf gs rfl hnd hcover x

theorem giantSignedGhostProductSimultaneous_eq_univWord
    {B : Type u} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemoryGroups P → ℂ) (hf : GiantSignedGhostProductExponential f)
    (x : GiantSignedMemoryGroups P) :
    giantSignedGhostProductSimultaneousApply ν A C D f x =
      giantSignedGhostCoordinateWord ν A C D Finset.univ.toList f x :=
  giantSignedGhostProductSimultaneous_eq_coordinateWord ν hν A C D f hf _
    (Finset.nodup_toList _) (fun g => by simp) x

theorem giantSignedGhostSimultaneous_eq_memoryApply
    {B : Type u} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf w : ℝ) (hCf : 0 ≤ Cf) (hw : 0 < w)
    (hf : ∀ m, ‖f m‖ ≤ Cf * w ^ (∑ g, m.1 g)) (m : GiantSignedMemory P) :
    giantSignedGhostSimultaneousApply ν A C D f m =
      giantSignedGhostMemoryApply ν A C D f m := by
  let F := fun x => f ((giantSignedMemoryGroupEquiv P).symm x)
  have hF : GiantSignedGhostProductExponential F :=
    ⟨Cf, w, hCf, hw, fun x => hf ((giantSignedMemoryGroupEquiv P).symm x)⟩
  have h := giantSignedGhostProductSimultaneous_eq_univWord ν hν A C D F hF
    (giantSignedMemoryGroupEquiv P m)
  simpa only [giantSignedGhostSimultaneousApply, giantSignedGhostMemoryApply,
    giantSignedGhostProductSimultaneousApply, giantSignedGhostMemoryMoveCoefficient,
    giantSignedGhostMemoryMoveTarget] using h

end
end ArtinMatthews
