module

public import ArtinMatthews.SourceKPLocalCompactProductEvaluation
public import ArtinMatthews.SourceKPLocalCompactProductBorel


set_option backward.privateInPublic true
@[expose] public section

/-! The simultaneous compact picture uses one finite carrier for all
retained places and every spectral parameter. Its generators are the
actual parameter-zero coset values translated by the actual cube classes. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SourceKPLocalCompactProductLabel :=
  SourceKPLocalCompactProductCubeClasses K S × SourceKPLocalCompactProductCosets K hζ S

local notation "G" => SourceKPAdelicProjective K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "F" => sourceKPAdelicCompactSection K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "E" => sourceKPLocalCompactTorusFlatEquiv K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Bₛ" => SourceKPLocalCompactProductBorel K hζ S
local notation "Cₛ" => SourceKPLocalCompactProductCompact K hζ S
local notation "Qₛ" => SourceKPLocalCompactProductCosets K hζ S
local notation "Q" => SourceKPLocalCompactProductLabel K hζ S
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S
local notation "D" => sourceKPLocalCompactProductCubeBorel K hζ S
local notation "eval" => sourceKPLocalCompactProductEvaluation K hζ S

local instance sourceKPLocalCompactProductCarrierAddCommGroup (s : ℂ) : AddCommGroup (V s) :=
  Submodule.addCommGroup _

theorem sourceKPLocalCompactProductLabel_finite : Finite Q := by
  let : Finite (SourceKPLocalCompactProductCubeClasses K S) :=
    sourceKPLocalCompactProductCubeClasses_finite K S
  let : Finite Qₛ := sourceKPLocalCompactProductCosets_finite K hζ S
  exact inferInstanceAs (Finite (SourceKPLocalCompactProductCubeClasses K S × Qₛ))

theorem sourceKPLocalCompactProductLabel_card :
    Nat.card Q =
      (∏ P : S, Nat.card (SourceKPLocalCompactCubeClasses K P.val)) *
        ∏ P : S, Nat.card (sourceKPLocalCompactCover K hζ P.val ⧸
          sourceKPLocalCompactDeep K hζ P.val) := by
  rw [SourceKPLocalCompactProductLabel,Nat.card_prod,
    sourceKPLocalCompactProductCubeClasses_card K S,
    sourceKPLocalCompactProductCosets_card K hζ S]

def sourceKPLocalCompactProductSeed (r : G) (q : Q) : V 0 :=
  ρ 0 (Lᴮ (D q.1)) (eval 0 r q.2)

local notation "seed" => sourceKPLocalCompactProductSeed K hζ S

def sourceKPLocalCompactProductCarrier (r : G) : Submodule ℂ (V 0) :=
  Submodule.span ℂ (Set.range (seed r))

local notation "W" => sourceKPLocalCompactProductCarrier K hζ S

theorem sourceKPLocalCompactProductCarrier_finiteDimensional (r : G) :
    FiniteDimensional ℂ (W r) := by
  let : Finite Q := sourceKPLocalCompactProductLabel_finite K hζ S
  exact Module.Finite.span_of_finite ℂ (Set.finite_range (seed r))

theorem sourceKPLocalCompactProductCarrier_finrank_le (r : G) :
    Module.finrank ℂ (W r) ≤ Nat.card Q := by
  let : Finite Q := sourceKPLocalCompactProductLabel_finite K hζ S
  let : Fintype Q := Fintype.ofFinite _
  let : Fintype (Set.range (seed r)) := Fintype.ofFinite _
  refine (finrank_span_le_card (Set.range (seed r))).trans ?_
  rw [Set.toFinset_card,Nat.card_eq_fintype_card]
  convert Fintype.card_range_le (seed r)

theorem sourceKPLocalCompactProductCarrier_invariant (r : G) (b : Bₛ)
    (v : V 0) (hv : v ∈ W r) : ρ 0 (Lᴮ b) v ∈ W r := by
  change v ∈ Submodule.span ℂ (Set.range (seed r)) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q,rfl⟩ := hv
    let w : V 0 := eval 0 r q.2
    let b₀ : Bₛ := D q.1
    have he : ρ 0 (Lᴮ b) (ρ 0 (Lᴮ b₀) w) = ρ 0 (Lᴮ (b*b₀)) w := by
      rw [map_mul Lᴮ,map_mul (ρ 0),Module.End.mul_apply]
    obtain ⟨c,a,ha⟩ := sourceKPLocalCompactProductBorelAction_cubeClasses K hζ S 0 (b*b₀)
    change ρ 0 (Lᴮ b) (ρ 0 (Lᴮ b₀) w) ∈ W r
    rw [he,ha w]
    exact (W r).smul_mem (a : ℂ) (Submodule.subset_span ⟨(c,q.2),rfl⟩)
  | zero => simpa only [map_zero] using (W r).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (W r).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (W r).smul_mem a hx

theorem sourceKPLocalCompactProductSection_flat_seed (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (s : ℂ) (g : Gₛ) :
    ∃ (q : Q) (a : ℂˣ), (E s).symm ((F s).val (L g*r)) = (a : ℂ) • seed r q := by
  obtain ⟨b,k,hg⟩ := sourceKPLocalCompactProductCover_Iwasawa K hζ S g
  let q₀ : Qₛ := fun P => QuotientGroup.mk (k P)
  have hv : (F 0).val (L g*r) = ρ 0 (Lᴮ b) ((F 0).val (L (fun P => (k P).val)*r)) := by
    rw [hg]
    exact sourceKPLocalCompactProductSection_borel K hζ S 0 r b (fun P => (k P).val)
  have hz : (F 0).val (L g*r) = ρ 0 (Lᴮ b) (eval 0 r q₀) :=
    hv.trans (congrArg (ρ 0 (Lᴮ b))
      (sourceKPLocalCompactProductEvaluation_apply K hζ S 0 r hr k).symm)
  obtain ⟨q₁,a,ha⟩ := sourceKPLocalCompactProductBorelAction_cubeClasses K hζ S 0 b
  obtain ⟨c,hc⟩ := sourceKPLocalCompactSection_flat K hζ s (L g*r)
  have he : (E s).symm ((F s).val (L g*r)) = (c : ℂ) • (F 0).val (L g*r) := by
    rw [hc]
    exact ((E s).symm.toLinearMap.map_smul (c : ℂ) _).trans
      (congrArg (fun v : V 0 => (c : ℂ) • v) ((E s).symm_apply_apply _))
  refine ⟨(q₁,q₀),c*a,?_⟩
  rw [he,hz,ha (eval 0 r q₀),smul_smul]
  rfl

theorem sourceKPLocalCompactProductSection_mem (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (s : ℂ) (g : Gₛ) :
    (E s).symm ((F s).val (L g*r)) ∈ W r := by
  obtain ⟨q,a,ha⟩ := sourceKPLocalCompactProductSection_flat_seed K hζ S r hr s g
  rw [ha]
  exact (W r).smul_mem (a : ℂ) (Submodule.subset_span ⟨q,rfl⟩)

def sourceKPLocalCompactProductRestriction (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (s : ℂ) (q : Qₛ) : W r :=
  ⟨(E s).symm (eval s r q),
    sourceKPLocalCompactProductSection_mem K hζ S r hr s (fun P => (q P).out.val)⟩

theorem sourceKPLocalCompactProductRestriction_apply (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1) (s : ℂ) (k : Cₛ) :
    (sourceKPLocalCompactProductRestriction K hζ S r hr s (fun P => QuotientGroup.mk (k P))).val =
      (E s).symm ((F s).val (L (fun P => (k P).val)*r)) :=
  congrArg (E s).symm (sourceKPLocalCompactProductEvaluation_apply K hζ S s r hr k)

theorem sourceKPLocalCompactProductRestriction_covariant (r : G)
    (hr : ∀ P : S, sourceKPAdelicLocalBase K hζ P.val r = 1)
    (s : ℂ) (b : Bₛ) (hb : ∀ P : S, (b P).val ∈ sourceKPLocalCompactCover K hζ P.val)
    (k : Cₛ) :
    (sourceKPLocalCompactProductRestriction K hζ S r hr s
      (fun P => QuotientGroup.mk ((⟨(b P).val,hb P⟩ : sourceKPLocalCompactCover K hζ P.val)*k P))).val =
      ρ 0 (Lᴮ b) (sourceKPLocalCompactProductRestriction K hζ S r hr s
        (fun P => QuotientGroup.mk (k P))).val := by
  rw [sourceKPLocalCompactProductRestriction_apply K hζ S r hr,
    sourceKPLocalCompactProductRestriction_apply K hζ S r hr]
  apply (E s).injective
  rw [(E s).apply_symm_apply,← sourceKPLocalCompactProductBorelFlat_action K hζ S s b hb,
    (E s).apply_symm_apply]
  exact sourceKPLocalCompactProductSection_borel K hζ S s r b (fun P => (k P).val)

theorem sourceKPLocalCompactProductRestriction_finiteDimensional (r : G) :
    FiniteDimensional ℂ (Qₛ → W r) := by
  let : Finite Qₛ := sourceKPLocalCompactProductCosets_finite K hζ S
  let : FiniteDimensional ℂ (W r) := sourceKPLocalCompactProductCarrier_finiteDimensional K hζ S r
  infer_instance

end
end ArtinMatthews
