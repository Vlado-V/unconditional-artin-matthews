module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.FinitePositionInsert
public import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLattices
public import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner


set_option backward.privateInPublic true
@[expose] public section

/-! # Finite Test Support -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The finite function of a restricted Bruhat family has compact support.
A single nonzero algebraic integer clears all exceptional local supports. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_denominator (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a : Fin N → ArchimedeanAdeles.Construction.FiniteAdeles F, f.finiteValue F N a ≠ 0 →
      ∀ i, algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a i ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      IsCompact (tsupport (f (.inr v)).val) :=
    (NonarchimedeanIntertwiner.LocalAnalysis.schwartzBruhat_totallyDisconnected_iff.mp (f (.inr v)).property).2
  choose d hd hb using fun v => LocalCompact.Construction.compact_local_integer_denominator F v N _ (hlocal v)
  have hs := eventually_cofinite.mp f.unramified
  let s := hs.toFinset
  let r : 𝓞 F := ∏ v ∈ s, d v
  refine ⟨r, Finset.prod_ne_zero_iff.mpr (fun v _ => hd v), fun a ha i v => ?_⟩
  have hnz (w : HeightOneSpectrum (𝓞 F)) : (f (.inr w)).val (fun j => a j w) ≠ 0 := by
    intro hw
    exact ha (tprod_of_exists_eq_zero ⟨w, hw⟩)
  change algebraMap (𝓞 F) (v.adicCompletion F) r * a i v ∈ v.adicCompletionIntegers F
  by_cases hv : v ∈ s
  · have hbound := hb v (subset_tsupport _ (hnz v))
    have hdv : d v ∣ r := Finset.dvd_prod_of_mem d hv
    exact LocalCompact.Construction.localIntegerPositionBox_mono F v N hdv hbound i
  · have hf : f (.inr v) = Vacuum.Construction.finiteVacuum F N v := by simpa [s] using hv
    have hint : ∀ j, a j v ∈ v.adicCompletionIntegers F := by
      by_contra hh
      apply hnz v
      rw [hf]
      exact FinitePositionInsert.Construction.finiteVacuum_eq_zero_of_not_integral F N v _ hh
    exact (v.adicCompletionIntegers F).toSubring.mul_mem
      (coe_mem_adicCompletionIntegers (K := F) v r) (hint i)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.finiteValue_compactSupport (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    HasCompactSupport (f.finiteValue F N) := by
  obtain ⟨r, hr, hb⟩ := f.finiteValue_denominator F N
  let q := algebraMap (𝓞 F) F r
  have hq : q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  apply HasCompactSupport.intro (FiniteLattices.Construction.finiteAdelicPositionLattice_isCompact q⁻¹ (inv_ne_zero hq))
  intro a ha
  by_contra hnz
  apply ha
  apply (FiniteLattices.Construction.finiteAdelicPositionLattice_mem_iff q⁻¹ (inv_ne_zero hq) a).mpr
  intro i
  have hh := hb a hnz i
  change algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (q⁻¹)⁻¹ * a i ∈ IntegralAdeles.Construction.finiteIntegralRing F
  rw [inv_inv]
  simpa only [q, IsScalarTower.algebraMap_apply] using! hh

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
