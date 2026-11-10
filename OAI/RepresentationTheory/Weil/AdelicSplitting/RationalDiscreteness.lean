module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! # Rational Discreteness -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness.Construction

noncomputable section

/-! Finiteness of rational points in compact adelic sets. Finite-place
supports clear denominators; the archimedean images then lie in an actual
Minkowski integer lattice. -/

open scoped _root_.NumberField Classical
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem compact_finiteAdeles_common_denominator (K : Set (ArchimedeanAdeles.Construction.FiniteAdeles F)) (hK : IsCompact K) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a ∈ K,
      algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
  have hc : Continuous (fun a : ArchimedeanAdeles.Construction.FiniteAdeles F => fun _ : Unit => a) :=
    continuous_pi (fun _ => continuous_id)
  obtain ⟨r, hr, hKr⟩ := IntegralAdeles.Construction.compact_subset_finiteIntegralBox F _ (hK.image hc)
  exact ⟨r, hr, fun a ha => hKr (Set.mem_image_of_mem _ ha) ()⟩

theorem finite_rational_preimage_compact (K : Set (ArchimedeanAdeles.Construction.Adeles F)) (hK : IsCompact K) :
    Set.Finite {q : F | algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q ∈ K} := by
  obtain ⟨r, hr, hKr⟩ := compact_finiteAdeles_common_denominator F _
    (hK.image (continuous_snd : Continuous (fun a : ArchimedeanAdeles.Construction.Adeles F => a.2)))
  let rF := algebraMap (𝓞 F) F r
  have hrF : rF ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  let f : ArchimedeanAdeles.Construction.Adeles F → mixedEmbedding.mixedSpace F := fun a =>
    mixedEmbedding F rF * ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F a.1
  have hf : Continuous f := continuous_const.mul
    ((ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).continuous.comp continuous_fst)
  let T := f '' K
  have hT : IsCompact T := hK.image hf
  have hfinite : Set.Finite (T ∩ mixedEmbedding.integerLattice F) := by
    rw [← mixedEmbedding.span_latticeBasis F]
    exact ZSpan.setFinite_inter (mixedEmbedding.latticeBasis F) hT.isBounded
  let g : F → mixedEmbedding.mixedSpace F := fun q => mixedEmbedding F (rF * q)
  have hg : Function.Injective g := (mixedEmbedding_injective F).comp (mul_right_injective₀ hrF)
  apply Set.Finite.of_finite_image (f := g) _ (Set.injOn_of_injective hg)
  apply hfinite.subset
  rintro _ ⟨q, hq, rfl⟩
  constructor
  · refine ⟨algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q, hq, ?_⟩
    dsimp only [f, g]
    rw [map_mul, ← ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph_rational F q]
    rfl
  · have hqr : algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (rF * q) ∈ IntegralAdeles.Construction.finiteIntegralRing F := by
      have hh := hKr _ (Set.mem_image_of_mem Prod.snd hq)
      simpa only [map_mul, rF, ← IsScalarTower.algebraMap_apply] using! hh
    obtain ⟨b, hb⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff F (rF * q)).mp hqr
    change ∃ b : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F b) = g q
    exact ⟨b, congrArg (mixedEmbedding F) hb⟩

theorem finite_rational_positions_preimage_compact {ι : Type*} [Fintype ι]
    (K : Set (ι → ArchimedeanAdeles.Construction.Adeles F)) (hK : IsCompact K) :
    Set.Finite {q : ι → F | (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) ∈ K} := by
  let S : ι → Set F := fun i => {q | algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q ∈ (fun a : ι → ArchimedeanAdeles.Construction.Adeles F => a i) '' K}
  have hS : ∀ i, (S i).Finite := fun i =>
    finite_rational_preimage_compact F _ (hK.image (continuous_apply i))
  apply (Set.Finite.pi hS).subset
  intro q hq i _
  exact Set.mem_image_of_mem (fun a : ι → ArchimedeanAdeles.Construction.Adeles F => a i) hq

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness.Construction
