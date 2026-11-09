module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedJacquetProfile


set_option backward.privateInPublic true
@[expose] public section

/-! The actual deep level makes the retained profiles constant on
right compact cosets. The finite quotient gives one support cutoff
and small-norm bound for all basis labels and compact inputs. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped BigOperators Classical SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "s₀" => (1 / 6 : ℂ)
local notation "L" => P.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "Cpt" => sourceKPLocalCompactCover K hζ P
local notation "Deep" => sourceKPLocalCompactDeep K hζ P
local notation "Q" => (Cpt ⧸ Deep)
local notation "a₀" => (fun z : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal z))
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
  (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K))) s₀ hs
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "C" => sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P s₀ hs
local notation "hC" => sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P s₀ hs
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P s₀ hs
local notation "v₀" => sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P s₀ hs
local notation "J" => sourceKPAdelicOutgoingRegularizedLocalJacquetMap K hζ P s₀ hs
local notation "π" => sourceKPJacquetRight K hζ P ρ₀ C hC
local notation "coord" => sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate K hζ P hs
local notation "Index" => SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ P hs
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ P hs

local instance sourceKPAdelicOutgoingRetainedCompactProfilesAddCommGroup : AddCommGroup W :=
  Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_compact_coset
    (k : Index) (a : G₀) (b b' : Cpt)
    (h : (QuotientGroup.mk b : Q) = QuotientGroup.mk b') :
    F k (a*b.val) = F k (a*b'.val) := by
  let j : Deep := ⟨b⁻¹*b', QuotientGroup.eq.mp h⟩
  have hb : b.val*j.val.val = b'.val :=
    congrArg (fun c : Cpt => c.val) (mul_inv_cancel_left b b')
  funext z
  have he : π (a₀ z*(a*b.val)) v₀ = π (a₀ z*(a*b'.val)) v₀ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (R₀).val.val (x*(a₀ z*(a*b.val))) = (R₀).val.val (x*(a₀ z*(a*b'.val)))
    have hx : x*(a₀ z*(a*b'.val)) = (x*(a₀ z*(a*b.val)))*j.val.val := by
      rw [← hb]
      simp only [mul_assoc]
    exact (sourceKPLocalCompactFixedSpace_right K hζ P ρ₀ R₀ (x*(a₀ z*(a*b.val))) j).symm.trans
      (congrArg (R₀).val.val hx.symm)
  exact congrArg (fun f : C => coord k (J f)) he

theorem sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_compact_uniform
    {I : Type*} [Finite I] (a : I → G₀) :
    ∃ n : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ (i : I) (k : Index) (b : Cpt),
      Continuous (F k (a i*b.val)) ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P (n : ℤ) → F k (a i*b.val) z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 →
        ‖F k (a i*b.val) z‖ ≤ M * ‖(z : L)‖ ^ (1 / 3 : ℝ) := by
  let : Fintype I := Fintype.ofFinite I
  let : Finite Q := sourceKPLocalCompactCosets_finite K hζ P
  let : Fintype Q := Fintype.ofFinite Q
  let D := I × Index × Q
  let f : D → Lˣ → ℂ := fun d => F d.2.1 (a d.1*d.2.2.out.val)
  have hD (d : D) := (sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_data K hζ P hs
    d.2.1 (a d.1*d.2.2.out.val)).2
  choose n M hM hSupport hBound using hD
  let N : ℕ := ∑ d : D, (n d).natAbs
  let A : ℝ := 1 + ∑ d : D, M d
  have hA : 0 < A := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun d _ => (hM d).le)
  have hn (d : D) : n d ≤ (N : ℤ) := by
    have h₀ : n d ≤ ((n d).natAbs : ℤ) := Int.le_natAbs
    refine h₀.trans ?_
    exact_mod_cast (Finset.single_le_sum (f := fun e : D => (n e).natAbs)
      (fun e _ => Nat.zero_le _) (Finset.mem_univ d))
  have hA' (d : D) : M d ≤ A := by
    have hle := Finset.single_le_sum (f := M) (fun e _ => (hM e).le) (Finset.mem_univ d)
    exact hle.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨N,A,hA,fun i k b => ?_⟩
  let d : D := (i,k,QuotientGroup.mk b)
  have he : f d = F k (a i*b.val) :=
    sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_compact_coset K hζ P hs k
      (a i) (QuotientGroup.mk b : Q).out b (QuotientGroup.out_eq' _)
  refine ⟨(sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_data K hζ P hs k (a i*b.val)).1,?_,?_⟩
  · intro z hz
    have hnot : z ∉ sourceLocalMulBall K P (n d) := fun hmem =>
      hz (sourceKPJacquetSelfDual_ball_mono K P (hn d) hmem)
    exact (congrFun he z).symm.trans (hSupport d z hnot)
  · intro z hz
    rw [← congrFun he z]
    exact (hBound d z hz).trans (mul_le_mul_of_nonneg_right (hA' d)
      (Real.rpow_nonneg (norm_nonneg _) _))

end
end ArtinMatthews
