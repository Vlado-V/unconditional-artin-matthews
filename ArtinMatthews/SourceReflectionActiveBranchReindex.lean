module

public import ArtinMatthews.SourceReflectionFrozenWeights
public import ArtinMatthews.SourceReflectionExteriorSupport
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

/-! Every simple prime is active. The optional branches on the powerful
support are exactly the original active choices, with their simple
support adjoined disjointly. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain Finset
open scoped NumberField Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "active" => sourceReflectionActiveChoices K S₀

theorem sourceReflectionSimpleSupport_subset_activeChoice {h d : E}
    (hd : sourceReflectionIsSquarefree d) (hdis : Disjoint h.support d.support)
    {g : Finset PE} (hg : g ∈ active (h+d)) : d.support ⊆ g := by
  intro P hP
  have hP' : P ∈ (h+d).support := (sourceReflectionExteriorRow_mem K S₀ h d P).mpr (mem_union_right _ hP)
  have hmod : (h+d) P % 6 = 1 :=
    congrArg Fin.val (sourceReflectionDigitIndex_row K S₀ hd hdis.symm hP)
  exact (mem_filter.mp hg).2 P hP' (hmod.trans_ne (by decide))

theorem sourceReflectionActiveChoice_union_simple {h d : E}
    {f : Finset PE} (hf : f ∈ active h) :
    f ∪ d.support ∈ active (h+d) := by
  obtain ⟨hfs,hfmod⟩ := mem_filter.mp hf
  have hs : f ⊆ h.support := mem_powerset.mp hfs
  refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
  · intro P hP
    exact (sourceReflectionExteriorRow_mem K S₀ h d P).mpr
      (mem_union.mpr ((mem_union.mp hP).imp (fun hp => hs hp) id))
  · intro P hP hmod
    by_cases hp : P ∈ d.support
    · exact mem_union_right _ hp
    · have hp' := (mem_union.mp ((sourceReflectionExteriorRow_mem K S₀ h d P).mp hP)).resolve_right hp
      exact mem_union_left _ (hfmod P hp' (by
        simpa only [Finsupp.add_apply, Finsupp.notMem_support_iff.mp hp, add_zero] using hmod))

theorem sourceReflectionActiveChoice_sdiff_simple {h d : E} {g : Finset PE}
    (hdis : Disjoint h.support d.support) (hg : g ∈ active (h+d)) : g \ d.support ∈ active h := by
  obtain ⟨hgs,hgmod⟩ := mem_filter.mp hg
  have hs : g ⊆ (h+d).support := mem_powerset.mp hgs
  refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
  · intro P hP
    obtain ⟨hp,hd⟩ := mem_sdiff.mp hP
    exact (mem_union.mp ((sourceReflectionExteriorRow_mem K S₀ h d P).mp (hs hp))).resolve_right hd
  · intro P hP hmod
    have hPd : P ∉ d.support := disjoint_left.mp hdis hP
    exact mem_sdiff.mpr ⟨hgmod P ((sourceReflectionExteriorRow_mem K S₀ h d P).mpr
      (mem_union_left _ hP)) (by
        simpa only [Finsupp.add_apply, Finsupp.notMem_support_iff.mp hPd, add_zero] using hmod), hPd⟩

theorem sourceReflectionActiveChoices_add_image {h d : E}
    (hd : sourceReflectionIsSquarefree d) (hdis : Disjoint h.support d.support) :
    (active h).image (fun f => f ∪ d.support) = active (h+d) := by
  ext g
  rw [mem_image]
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact sourceReflectionActiveChoice_union_simple K S₀ hf
  · intro hg
    have hdg := sourceReflectionSimpleSupport_subset_activeChoice K S₀ hd hdis hg
    exact ⟨g \ d.support, sourceReflectionActiveChoice_sdiff_simple K S₀ hdis hg,
      sdiff_union_of_subset hdg⟩

theorem sourceReflectionActiveBranch_sum_add {A : Type*} [AddCommMonoid A] {h d : E}
    (hd : sourceReflectionIsSquarefree d) (hdis : Disjoint h.support d.support)
    (F : Finset PE → A)
    (hF : ∀ g ∈ (h+d).support.powerset, g ∉ active (h+d) → F g = 0) :
    (∑ g ∈ (h+d).support.powerset, F g) =
      ∑ f ∈ active h, F (f ∪ d.support) := by
  calc
    _ = ∑ g ∈ active (h+d), F g :=
      (sum_subset (filter_subset _ _) hF).symm
    _ = _ := by
      rw [← sourceReflectionActiveChoices_add_image K S₀ hd hdis, sum_image]
      intro f hf g hg he
      have hsub (s : Finset PE) (hs : s ∈ active h) : s ⊆ h.support :=
        sourceReflectionActiveChoice_subset K S₀ hs
      have he' (s : Finset PE) (hs : s ∈ active h) : (s ∪ d.support) \ d.support = s := by
        ext P
        simp only [mem_sdiff, mem_union]
        constructor
        · rintro ⟨hp,hn⟩
          exact hp.resolve_right hn
        · intro hp
          exact ⟨Or.inl hp, disjoint_left.mp hdis (hsub s hs hp)⟩
      exact (he' f hf).symm.trans
        ((congrArg (fun s : Finset PE => s \ d.support) he).trans (he' g hg))

theorem sourceReflectionActiveBranch_sum_powerfulSimple {A : Type*} [AddCommMonoid A] (e : E)
    (F : Finset PE → A) (hF : ∀ g ∈ e.support.powerset, g ∉ active e → F g = 0) :
    (∑ g ∈ e.support.powerset, F g) =
      ∑ f ∈ active (sourceReflectionPowerfulPart e), F (f ∪ (sourceReflectionSimplePart e).support) := by
  have he := sourceReflectionPowerfulSimple_add e
  simpa only [he] using
    (sourceReflectionActiveBranch_sum_add K S₀ (sourceReflectionSimplePart_squarefree e)
      (sourceReflectionPowerfulSimple_disjoint e) F
      (by simpa only [he] using hF))

end
end ArtinMatthews.SourceEulerAssembly
