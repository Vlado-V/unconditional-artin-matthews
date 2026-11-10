module

public import ArtinMatthews.SourceKPLocalCompactProductLift
public import ArtinMatthews.SourceKPLocalCompactBorelOrbit
public import ArtinMatthews.SourceKPLocalCompactFlatTorus
public import ArtinMatthews.SourceKPAdelicFlatTorus
public import ArtinMatthews.SourceKPLocalCompactCubeAction
public import ArtinMatthews.SourceKPLocalCompactFlatBorel
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Simultaneous retained Borel actions have a finite cube-class
description, with the actual central and cube scalars. On the
compact intersections the global norm twist is exactly one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical BigOperators
noncomputable section

private theorem sourceKPLocalCompactEnd_product_smul {ι V : Type*}
    [AddCommGroup V] [Module ℂ V] (T : Finset ι) (f g : ι → Module.End ℂ V)
    (hf : (T : Set ι).Pairwise (fun i j => Commute (f i) (f j)))
    (hg : (T : Set ι).Pairwise (fun i j => Commute (g i) (g j))) (a : ι → ℂ)
    (h : ∀ i ∈ T, f i = a i • g i) :
    T.noncommProd f hf = (∏ i ∈ T, a i) • T.noncommProd g hg := by
  induction T using Finset.induction_on with
  | empty =>
    change (1 : Module.End ℂ V) = (∏ i ∈ (∅ : Finset ι), a i) • (1 : Module.End ℂ V)
    rw [Finset.prod_empty,one_smul]
  | insert i T hi ih =>
    rw [Finset.noncommProd_insert_of_notMem T i f hf hi,
      Finset.noncommProd_insert_of_notMem T i g hg hi, Finset.prod_insert hi,
      h i (Finset.mem_insert_self i T)]
    have hf₀ := hf.mono (fun j (hj : j ∈ T) => Finset.mem_insert_of_mem hj)
    have hg₀ := hg.mono (fun j (hj : j ∈ T) => Finset.mem_insert_of_mem hj)
    rw [ih hf₀ hg₀ (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply,LinearMap.smul_apply,map_smul,smul_smul]
    rw [mul_comm (∏ j ∈ T, a j) (a i)]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SourceKPLocalCompactProductCubeClasses :=
  (P : S) → SourceKPLocalCompactCubeClasses K P.val

local notation "Qₛ" => SourceKPLocalCompactProductCubeClasses K S
local notation "B" => sourceKPAdelicCoveringBorel K hζ
local notation "Bₛ" => SourceKPLocalCompactProductBorel K hζ S
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S
local notation "ιᴮ" => sourceKPAdelicLocalBorel K hζ
local notation "E" => sourceKPLocalCompactTorusFlatEquiv K hζ

local instance sourceKPLocalCompactProductBorelAddCommGroup (s : ℂ) : AddCommGroup (V s) :=
  Submodule.addCommGroup _

theorem sourceKPLocalCompactProductCubeClasses_finite : Finite Qₛ := by
  letI (P : S) : Finite (SourceKPLocalCompactCubeClasses K P.val) :=
    sourceKPLocalCompactCubeClasses_finite K P.val
  exact inferInstanceAs (Finite ((P : S) → SourceKPLocalCompactCubeClasses K P.val))

theorem sourceKPLocalCompactProductCubeClasses_card :
    Nat.card Qₛ = ∏ P : S, Nat.card (SourceKPLocalCompactCubeClasses K P.val) :=
  Nat.card_pi

def sourceKPLocalCompactProductCubeBorel (q : Qₛ) : Bₛ :=
  fun P => sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (q P).out

local notation "D" => sourceKPLocalCompactProductCubeBorel K hζ S

theorem sourceKPLocalCompactProductBorelAction_cubeClasses (s : ℂ) (b : Bₛ) :
    ∃ (q : Qₛ) (a : ℂˣ), ∀ v : V s, ρ s (Lᴮ b) v = (a : ℂ) • ρ s (Lᴮ (D q)) v := by
  choose q a h using fun P : S =>
    sourceKPLocalCompactBorelAction_cubeClass K hζ P.val s (b P)
  let T : Finset S := Finset.univ
  let R (b₀ : Bₛ) : S → Module.End ℂ (V s) := fun P => ρ s (ιᴮ P.val (b₀ P))
  have hcomm (b₀ : Bₛ) : (T : Set S).Pairwise (fun P Q => Commute (R b₀ P) (R b₀ Q)) := by
    intro P _ Q _ hPQ
    have hc : Commute (ιᴮ P.val (b₀ P)) (ιᴮ Q.val (b₀ Q)) := by
      apply Subtype.ext
      exact (sourceKPAdelicLocalProjective_commute K hζ P.val Q.val
        (fun he => hPQ (Subtype.ext he.symm)) (b₀ P).val (b₀ Q).val).eq
    exact hc.map (ρ s)
  have hprod (b₀ : Bₛ) : ρ s (Lᴮ b₀) = T.noncommProd (R b₀) (hcomm b₀) := by
    rw [sourceKPLocalCompactProductBorelLift_noncommProd K hζ S]
    exact Finset.map_noncommProd _ _ _ (ρ s)
  have he (P : S) (_ : P ∈ T) : R b P = (a P : ℂ) • R (D q) P := by
    apply LinearMap.ext
    intro v
    exact h P v
  have hR : ρ s (Lᴮ b) = (∏ P ∈ T, (a P : ℂ)) • ρ s (Lᴮ (D q)) := by
    rw [hprod b,hprod (D q)]
    exact sourceKPLocalCompactEnd_product_smul T _ _ _ _ (fun P => (a P : ℂ)) he
  refine ⟨q,∏ P ∈ T, a P,fun v => ?_⟩
  simpa only [LinearMap.smul_apply,Units.coe_prod] using
    congrArg (fun u : Module.End ℂ (V s) => u v) hR

theorem sourceKPLocalCompactProductBorelFlat_action (s : ℂ) (b : Bₛ)
    (hb : ∀ P : S, (b P).val ∈ sourceKPLocalCompactCover K hζ P.val) (v : V 0) :
    ρ s (Lᴮ b) (E s v) = E s (ρ 0 (Lᴮ b) v) := by
  let α : B →* ℂˣ := (sourceKPLocalCompactTorusNorm K hζ s).comp
    (sourceKPAdelicBorelTorusProjection K hζ)
  have hα : α (Lᴮ b) = 1 := by
    rw [sourceKPLocalCompactProductBorelLift_noncommProd K hζ S]
    erw [Finset.map_noncommProd]
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro P _
    change sourceKPIdeleComplexNorm K s (sourceKPAdelicTorusIdele K hζ
      (sourceKPAdelicBorelTorusProjection K hζ (ιᴮ P.val (b P)))) = 1
    exact sourceKPIdeleComplexNorm_of_norm_one K s _
      (sourceKPLocalCompactBorelTorus_norm_one K hζ P.val (b P) (hb P))
  have h := sourceKPLocalCompactTorusFlatEquiv_action K hζ s (Lᴮ b) v
  change ρ s (Lᴮ b) (E s v) = (α (Lᴮ b) : ℂ) • E s (ρ 0 (Lᴮ b) v) at h
  rw [hα,Units.val_one,one_smul] at h
  exact h

end
end ArtinMatthews
