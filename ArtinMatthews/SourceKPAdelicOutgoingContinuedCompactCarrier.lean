module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuedCompactTranslate
public import ArtinMatthews.SourceKPLocalCompactProductCarrier


set_option backward.privateInPublic true
@[expose] public section

/-! One finite carrier describes the actual regularized evaluations
as functions of every exterior remainder at once. The cube-class
scalar is chosen from the retained tuple and is independent of the
remainder, which keeps all global coefficient dependence intact. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SourceKPAdelicOutgoingRetainedRest :=
  {r : SourceKPAdelicProjective K hζ // ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1}

local notation "Rest" => SourceKPAdelicOutgoingRetainedRest K hζ S
local notation "Vₚ" => SourceKPAdelicPrincipalSeries K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Qₛ" => SourceKPLocalCompactProductCosets K hζ S
local notation "Q" => SourceKPLocalCompactProductLabel K hζ S
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S
local notation "D" => sourceKPLocalCompactProductCubeBorel K hζ S
local notation "tr" => sourceKPAdelicOutgoingRegularizedCompactTranslate K hζ S

local instance sourceKPAdelicOutgoingContinuedCarrierAddCommGroup (s : ℂ) :
    AddCommGroup (V s) := Submodule.addCommGroup _

def sourceKPAdelicOutgoingRegularizedRetainedValue (s : ℂ) (hs : 0 < s.re) (g : Gₛ) :
    Rest → V (-s) :=
  fun r => (R s hs).val (L g*r.val)

local notation "value" => sourceKPAdelicOutgoingRegularizedRetainedValue K hζ S

def sourceKPAdelicOutgoingRegularizedRetainedSeed (s : ℂ) (hs : 0 < s.re) (q : Q) :
    Rest → V (-s) :=
  fun r => ρ (-s) (Lᴮ (D q.1)) ((tr s hs q.2).val r.val)

local notation "seed" => sourceKPAdelicOutgoingRegularizedRetainedSeed K hζ S

theorem sourceKPAdelicOutgoingRegularizedRetainedValue_eq_seed (s : ℂ) (hs : 0 < s.re) (g : Gₛ) :
    ∃ (q : Q) (a : ℂˣ), value s hs g = (a : ℂ) • seed s hs q := by
  obtain ⟨b,k,hg⟩ := sourceKPLocalCompactProductCover_Iwasawa K hζ S g
  let q : Qₛ := fun P => QuotientGroup.mk (k P)
  let k₀ : Gₛ := fun P => (k P).val
  obtain ⟨c,a,ha⟩ := sourceKPLocalCompactProductBorelAction_cubeClasses K hζ S (-s) b
  refine ⟨(c,q),a,?_⟩
  funext r
  have hcomp := congrArg (fun f : Vₚ (-s) => f.val r.val)
    (sourceKPAdelicOutgoingRegularizedCompactTranslate_apply K hζ S s hs k)
  change (tr s hs q).val r.val = (R s hs).val (r.val*L k₀) at hcomp
  have hcomm := sourceKPLocalCompactProductLift_commute_of_base_one K hζ S k₀ r.val r.property
  rw [← hcomm.eq] at hcomp
  have hcov := (R s hs).property (Lᴮ b) (L k₀*r.val)
  change (R s hs).val (L g*r.val) =
    (a : ℂ) • ρ (-s) (Lᴮ (D c)) ((tr s hs q).val r.val)
  rw [hg,map_mul L,mul_assoc,← sourceKPLocalCompactProductBorelLift_val K hζ S b,hcov,← hcomp]
  exact ha _

def sourceKPAdelicOutgoingRegularizedRetainedCarrier (s : ℂ) (hs : 0 < s.re) :
    Submodule ℂ (Rest → V (-s)) :=
  Submodule.span ℂ (Set.range (seed s hs))

local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S

theorem sourceKPAdelicOutgoingRegularizedRetainedCarrier_finiteDimensional (s : ℂ) (hs : 0 < s.re) :
    FiniteDimensional ℂ (W s hs) := by
  let : Finite Q := sourceKPLocalCompactProductLabel_finite K hζ S
  exact Module.Finite.span_of_finite ℂ (Set.finite_range (seed s hs))

theorem sourceKPAdelicOutgoingRegularizedRetainedCarrier_finrank_le (s : ℂ) (hs : 0 < s.re) :
    Module.finrank ℂ (W s hs) ≤ Nat.card Q := by
  let : Finite Q := sourceKPLocalCompactProductLabel_finite K hζ S
  let : Fintype Q := Fintype.ofFinite _
  let : Fintype (Set.range (seed s hs)) := Fintype.ofFinite _
  refine (finrank_span_le_card (Set.range (seed s hs))).trans ?_
  rw [Set.toFinset_card,Nat.card_eq_fintype_card]
  convert Fintype.card_range_le (seed s hs)

theorem sourceKPAdelicOutgoingRegularizedRetainedValue_mem (s : ℂ) (hs : 0 < s.re) (g : Gₛ) :
    value s hs g ∈ W s hs := by
  obtain ⟨q,a,ha⟩ := sourceKPAdelicOutgoingRegularizedRetainedValue_eq_seed K hζ S s hs g
  rw [ha]
  exact (W s hs).smul_mem (a : ℂ) (Submodule.subset_span ⟨q,rfl⟩)

end
end ArtinMatthews
