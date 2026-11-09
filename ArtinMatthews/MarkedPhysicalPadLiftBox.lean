module

public import ArtinMatthews.MarkedPhysicalPadLiftPrimitive
public import ArtinMatthews.MarkedPhysicalPadCollisionFlags
public import ArtinMatthews.MarkedPhysicalCanonicalRoots


set_option backward.privateInPublic true
@[expose] public section

/-! The physical box of the performed pad dyad contains both actual
lifted cofactor endpoints. The primitive and incidence flags are derived
from the original scalar support and the two distinctness flags. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosHyperbolaError

def markedPhysicalPadBox (d₀ Y Hm Hn : ℝ) : Finset (ℤ × ℤ) :=
  let U := d₀*Y*Hm
  markedPhysicalPrimitiveBox U (16*U) Hn (2*Hn)

theorem markedPhysicalPadBox_nonnegative {d₀ Y Hm Hn : ℝ}
    (hd₀ : 0 ≤ d₀) (hY : 0 ≤ Y) (hm : 0 ≤ Hm) (hn : 0 ≤ Hn) :
    ∀ z ∈ markedPhysicalPadBox d₀ Y Hm Hn,0 ≤ z.1 ∧ 0 ≤ z.2 := by
  intro z hz
  have hb := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
  have h₁ := ((fixedURoot_mem_closed_interval _ _ _).mp hb.1).1
  have h₂ := ((fixedURoot_mem_closed_interval _ _ _).mp hb.2).1
  have h₁' : 0 ≤ (z.1:ℝ) := (mul_nonneg (mul_nonneg hd₀ hY) hm).trans h₁
  have h₂' : 0 ≤ (z.2:ℝ) := hn.trans h₂
  exact ⟨by exact_mod_cast h₁',by exact_mod_cast h₂'⟩

theorem markedPhysicalPad_lift_mem_box {d₀ Y Hm Hn : ℝ} {D b m s : ℕ}
    (hd₀ : 0 ≤ d₀) (hY : 0 ≤ Y) (hm₀ : 0 ≤ Hm)
    (hD : d₀ ≤ (D:ℝ) ∧ (D:ℝ) < 2*d₀) (hb : Y ≤ (b:ℝ) ∧ (b:ℝ) ≤ 4*Y)
    (hm : Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) (hs : Hn ≤ (s:ℝ) ∧ (s:ℝ) ≤ 2*Hn)
    (hc : (D*b*m).Coprime s) :
    markedPhysicalLift (D*b) m s ∈ markedPhysicalPadBox d₀ Y Hm Hn := by
  unfold markedPhysicalPadBox markedPhysicalPrimitiveBox
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hc.isCoprime⟩
  · apply (fixedURoot_mem_closed_interval _ _ _).mpr
    simp only [markedPhysicalLift,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
    have h₁ := mul_le_mul hD.1 hb.1 hY (Nat.cast_nonneg D)
    have h₂ := mul_le_mul h₁ hm.1 hm₀ (by positivity : 0 ≤ (D:ℝ)*b)
    have h₃ := mul_le_mul hD.2.le hb.2 (Nat.cast_nonneg b) (by positivity : 0 ≤ 2*d₀)
    have h₄ := mul_le_mul h₃ hm.2 (Nat.cast_nonneg m) (by positivity : 0 ≤ 2*d₀*(4*Y))
    refine ⟨h₂,h₄.trans_eq ?_⟩
    ring
  · apply (fixedURoot_mem_closed_interval _ _ _).mpr
    simpa only [markedPhysicalLift,Int.cast_natCast] using hs

theorem markedPhysicalLift_stateCondition {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p ∈ P j → p.Prime) {M : ℕ} (a : MarkedPhysicalMarking P M)
    (ha : MarkedPhysicalMarkingDistinct a) {m s : ℕ}
    (hc : (markedPhysicalMarkingProduct a*m).Coprime s) :
    MarkedPhysicalStateCondition (markedPhysicalLift (markedPhysicalMarkingProduct a) m s) a := by
  refine ⟨hc.isCoprime,ha,?_⟩
  intro j k
  have hd : (a j k:ℕ) ∣ markedPhysicalMarkingProduct a :=
    (markedPhysicalMarkingProduct_prime_dvd_iff hP a (hP j _ (a j k).2)).mpr ⟨j,k,rfl⟩
  change ((a j k:ℕ):ℤ) ∣ ((markedPhysicalMarkingProduct a*m:ℕ):ℤ)
  exact_mod_cast (dvd_mul_of_dvd_left hd m)

theorem markedPhysicalPad_cofactor_lifts
    {J : Type*} [Fintype J] [Nonempty J] {P : J → Finset ℕ}
    (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads : ℕ} (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))
    {d₀ Y Hm Hn W : ℝ} (hd₀ : 0 ≤ d₀) (hY : 0 ≤ Y) (hm₀ : 0 ≤ Hm)
    (hD : d₀ ≤ (markedPhysicalMarkingProduct c:ℝ) ∧ (markedPhysicalMarkingProduct c:ℝ) < 2*d₀)
    (hb : Y ≤ (markedPrimeBandProduct P b:ℝ) ∧ (markedPrimeBandProduct P b:ℝ) ≤ 4*Y)
    (ha : Y ≤ (markedPrimeBandProduct P a:ℝ) ∧ (markedPrimeBandProduct P a:ℝ) ≤ 4*Y)
    (hbelow : ∀ j p,p ∈ P j → (p:ℝ)<W)
    (hgood : ∀ j,¬MarkedPadCollision {b j,a j} (c j)) (hne : ∀ j,b j ≠ a j)
    {m s r n : ℕ}
    (hm : Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm) (hr : Hm ≤ (r:ℝ) ∧ (r:ℝ) ≤ 2*Hm)
    (hs : Hn ≤ (s:ℝ) ∧ (s:ℝ) ≤ 2*Hn) (hn : Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn)
    (hmR : MarkedPhysicalBandRough P m) (hrR : MarkedPhysicalBandRough P r)
    (hsR : ∀ p : ℕ,p.Prime → p ∣ s → W ≤ (p:ℝ))
    (hnR : ∀ p : ℕ,p.Prime → p ∣ n → W ≤ (p:ℝ))
    (ht : |((markedPrimeBandProduct P b:ℤ)*m*n-(markedPrimeBandProduct P a:ℤ)*r*s:ℤ)| < W) :
    (∃ v : MarkedPhysicalCofactorCoordinates (Z := markedPhysicalPadBox d₀ Y Hm Hn)
      ((markedPhysicalMarkingSplit pads).symm (c,b)),v.1=(m,s)) ∧
    (∃ u : MarkedPhysicalCofactorCoordinates (Z := markedPhysicalPadBox d₀ Y Hm Hn)
      ((markedPhysicalMarkingSplit pads).symm (c,a)),u.1=(r,n)) := by
  obtain ⟨hcb,hca⟩ := markedPhysicalPad_lifts_coprime hP hdis b a c hbelow hne hmR hrR hsR hnR ht
  obtain ⟨hBs,_⟩ := (markedPhysicalPad_source_crossBan_iff hdis c b a).mpr ⟨hgood,hne⟩
  have hAs := markedPhysicalPad_target_distinct c b a hgood
  have hbprod := markedPhysicalPad_append_product P hP pads c b
  have haprod := markedPhysicalPad_append_product P hP pads c a
  have hz := markedPhysicalPad_lift_mem_box hd₀ hY hm₀ hD hb hm hs hcb
  have hw := markedPhysicalPad_lift_mem_box hd₀ hY hm₀ hD ha hr hn hca
  have hcB : (markedPhysicalMarkingProduct ((markedPhysicalMarkingSplit pads).symm (c,b))*m).Coprime s :=
    (congrArg (fun G : ℕ => (G*m).Coprime s) hbprod).mpr hcb
  have hcA : (markedPhysicalMarkingProduct ((markedPhysicalMarkingSplit pads).symm (c,a))*r).Coprime n :=
    (congrArg (fun G : ℕ => (G*r).Coprime n) haprod).mpr hca
  exact ⟨⟨⟨(m,s),by simpa only [hbprod,markedPrimeBandProduct] using hz,markedPhysicalLift_stateCondition hP _ hBs hcB⟩,rfl⟩,
    ⟨⟨(r,n),by simpa only [haprod,markedPrimeBandProduct] using hw,markedPhysicalLift_stateCondition hP _ hAs hcA⟩,rfl⟩⟩

end
end ArtinMatthews
