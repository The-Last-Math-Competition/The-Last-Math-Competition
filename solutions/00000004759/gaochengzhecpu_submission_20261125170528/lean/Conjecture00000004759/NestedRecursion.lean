import Conjecture00000004759.Basic
import Conjecture00000004759.FockModel

/-
  Conjecture 00000004759 — Speicher's Nested Operator-Valued Recursion, Central Factorization,
  and Computability of Polynomials of Depth at Most Three
  Core Lean 4.19.0 (zero external dependencies).
-/

namespace Conjecture00000004759

/-! ### 1. Recursive Decomposition of Noncrossing Partitions `NC(n)` & Nesting Depth -/

/-- Canonical first-block decomposition of a noncrossing partition. -/
inductive NCDecomp where
  | nil : NCDecomp
  | block : List NCDecomp → NCDecomp → NCDecomp
  deriving Repr

namespace NCDecomp

mutual
  def size : NCDecomp → Nat
    | .nil => 0
    | .block inners tail => (inners.length + 1) + sizeList inners + size tail

  def sizeList : List NCDecomp → Nat
    | [] => 0
    | p :: ps => size p + sizeList ps
end

mutual
  def nestingDepth : NCDecomp → Nat
    | .nil => 0
    | .block inners tail => Nat.max (1 + maxDepthList inners) (nestingDepth tail)

  def maxDepthList : List NCDecomp → Nat
    | [] => 0
    | p :: ps => Nat.max (nestingDepth p) (maxDepthList ps)
end

/-- Structural fuel recursion generating `(enumNC, enumSplits)` simultaneously for all sizes `≤ fuel`. -/
def enumAll : Nat → (Nat → List NCDecomp) × (Nat → List (List NCDecomp × NCDecomp))
  | 0 => (fun _ => [.nil], fun _ => [([], .nil)])
  | fuel + 1 =>
      let (ncF, spF) := enumAll fuel
      let ncNext : Nat → List NCDecomp
        | 0 => [.nil]
        | n + 1 => (spF n).foldr (fun (inners, tail) acc => .block inners tail :: acc) []
      let spNext : Nat → List (List NCDecomp × NCDecomp)
        | 0 => [([], .nil)]
        | b + 1 =>
            let caseEmpty := (ncNext (b + 1)).map (fun t => ([], t))
            let caseCons := (List.range (b + 1)).foldr (fun k acc =>
              let ps := ncF k
              let rests := spF (b - k)
              let combined := ps.foldr (fun p acc2 =>
                rests.map (fun (rs, t) => (p :: rs, t)) ++ acc2) []
              combined ++ acc) []
            caseEmpty ++ caseCons
      (ncNext, spNext)

/-- Enumerate all noncrossing partitions of exact size `n`. -/
def enumNC (n : Nat) : List NCDecomp := (enumAll n).1 n

/-- Verified Catalan numbers `|NC(n)| = 1, 2, 5, 14, 42, 132` for `n = 1..6` and
    nesting-depth counts (including minimal nested `n = 3` and minimal depth-3 `n = 5, 6`). -/
theorem nc_catalan_and_depth_counts :
    (enumNC 1).length = 1 ∧
    (enumNC 2).length = 2 ∧
    (enumNC 3).length = 5 ∧
    (enumNC 4).length = 14 ∧
    (enumNC 5).length = 42 ∧
    (enumNC 6).length = 132 ∧
    ((enumNC 2).filter (fun p => nestingDepth p == 2)).length = 0 ∧
    ((enumNC 3).filter (fun p => nestingDepth p == 2)).length = 1 ∧
    ((enumNC 4).filter (fun p => nestingDepth p == 2)).length = 6 ∧
    ((enumNC 4).filter (fun p => nestingDepth p == 3)).length = 0 ∧
    ((enumNC 5).filter (fun p => nestingDepth p == 3)).length = 1 ∧
    ((enumNC 6).filter (fun p => nestingDepth p == 3)).length = 10 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NCDecomp

/-! ### 2. Speicher's General Nested Operator-Valued Evaluation & Central Factorization -/

section SpeicherEval
variable {B : Type u} [AssocRing B]

mutual
  def evalNCStream (κ : Nat → List B → B) : NCDecomp → List B → (B × List B)
    | .nil, bs => (1, bs)
    | .block inners tail, bs =>
        let (args, bs₁) := evalGapsStream κ inners bs
        let vVal := κ inners.length args
        match tail with
        | .nil => (vVal, bs₁)
        | .block tInners tTail =>
            match bs₁ with
            | [] => (vVal, [])
            | bSep :: bs₂ =>
                let (tVal, bs₃) := evalNCStream κ (.block tInners tTail) bs₂
                (vVal * bSep * tVal, bs₃)

  def evalGapsStream (κ : Nat → List B → B) : List NCDecomp → List B → (List B × List B)
    | [], bs => ([], bs)
    | .nil :: rest, bs =>
        match bs with
        | [] => ([], [])
        | b :: bs₁ =>
            let (restArgs, bs₂) := evalGapsStream κ rest bs₁
            (b :: restArgs, bs₂)
    | .block pInners pTail :: rest, bs =>
        match bs with
        | [] => ([], [])
        | bOpen :: bs₁ =>
            let (midVal, bs₂) := evalNCStream κ (.block pInners pTail) bs₁
            match bs₂ with
            | [] => ([], [])
            | bClose :: bs₃ =>
                let (restArgs, bs₄) := evalGapsStream κ rest bs₃
                ((bOpen * midVal * bClose) :: restArgs, bs₄)
end

def evalNC (κ : Nat → List B → B) (π : NCDecomp) (bs : List B) : B :=
  (evalNCStream κ π bs).1

def listSum (xs : List B) : B :=
  xs.foldl (fun acc x => acc + x) 0

def sumOverNC (κ : Nat → List B → B) (n : Nat) (bs : List B) : B :=
  listSum ((NCDecomp.enumNC n).map (fun π => evalNC κ π bs))

mutual
  def blockWeightProd (c : Nat → B) : NCDecomp → B
    | .nil => 1
    | .block inners tail =>
        c (inners.length + 1) * blockWeightList c inners * blockWeightProd c tail

  def blockWeightList (c : Nat → B) : List NCDecomp → B
    | [] => 1
    | p :: ps => blockWeightProd c p * blockWeightList c ps
end

end SpeicherEval

/-! ### 3. Positive Central-Commutative Factorization Theorem -/

private theorem drop_append_exact {α : Type u} :
    ∀ (xs ys : List α) (m : Nat), (xs ++ ys).drop (xs.length + m) = ys.drop m
  | [], ys, m => by simp
  | _ :: xs, ys, m => by
      have h : (xs.length + 1) + m = (xs.length + m) + 1 := by omega
      change (_ :: (xs ++ ys)).drop ((xs.length + 1) + m) = ys.drop m
      rw [h]; exact drop_append_exact xs ys m

private theorem take_append_exact {α : Type u} :
    ∀ (xs ys : List α) (m : Nat), (xs ++ ys).take (xs.length + m) = xs ++ ys.take m
  | [], ys, m => by simp
  | x :: xs, ys, m => by
      have h : (xs.length + 1) + m = (xs.length + m) + 1 := by omega
      change (x :: (xs ++ ys)).take ((xs.length + 1) + m) = x :: (xs ++ ys.take m)
      rw [h]; dsimp; rw [take_append_exact xs ys m]

section CentralCommutative
variable {B : Type u} [CommAssocRing B]

private theorem comm_rearrange_mid (x y w z : B) :
    (x * (y * w)) * z = (x * y * z) * w := by
  rw [AssocRing.mul_assoc x (y * w) z,
      AssocRing.mul_assoc y w z,
      CommAssocRing.mul_comm w z,
      ← AssocRing.mul_assoc y z w,
      ← AssocRing.mul_assoc x (y * z) w,
      ← AssocRing.mul_assoc x y z]

private theorem comm_rearrange_pair (a₁ w₁ a₂ w₂ : B) :
    (a₁ * w₁) * (a₂ * w₂) = (a₁ * a₂) * (w₁ * w₂) := by
  rw [AssocRing.mul_assoc a₁ w₁ (a₂ * w₂),
      ← AssocRing.mul_assoc w₁ a₂ w₂,
      CommAssocRing.mul_comm w₁ a₂,
      AssocRing.mul_assoc a₂ w₁ w₂,
      ← AssocRing.mul_assoc a₁ a₂ (w₁ * w₂)]

mutual
  private theorem central_stream_eq (c : Nat → B) :
      ∀ (π : NCDecomp) (bs : List B),
        π.size ≥ 1 → bs.length ≥ π.size - 1 →
        evalNCStream (fun r args => listProd args * c (r + 1)) π bs =
          (listProd (bs.take (π.size - 1)) * blockWeightProd c π,
           bs.drop (π.size - 1))
    | .nil, _, hsz, _ => absurd hsz (by decide)
    | .block inners tail, bs, _, hlen => by
        cases tail with
        | nil =>
            have hneed : bs.length ≥ inners.length + NCDecomp.sizeList inners := by
              simp [NCDecomp.size] at hlen; omega
            obtain ⟨args, hgap1, hgap2⟩ := central_gaps_eq c inners bs hneed
            have hsz_eq : (NCDecomp.block inners .nil).size - 1 =
                inners.length + NCDecomp.sizeList inners := by
              simp [NCDecomp.size]; omega
            rw [hsz_eq]
            unfold evalNCStream
            rw [hgap1]
            dsimp
            rw [hgap2]
            refine Prod.ext ?_ rfl
            change listProd (bs.take (inners.length + NCDecomp.sizeList inners)) * blockWeightList c inners *
                c (inners.length + 1) =
              listProd (bs.take (inners.length + NCDecomp.sizeList inners)) *
                (c (inners.length + 1) * blockWeightList c inners * 1)
            rw [mul_one_ring,
                AssocRing.mul_assoc (listProd _) (blockWeightList c inners) (c (inners.length + 1)),
                CommAssocRing.mul_comm (blockWeightList c inners) (c (inners.length + 1))]
        | block tInners tTail =>
            have ht_sz : (NCDecomp.block tInners tTail).size ≥ 1 := by
              simp [NCDecomp.size]; omega
            have htot : (NCDecomp.block inners (.block tInners tTail)).size - 1 =
                (inners.length + NCDecomp.sizeList inners) +
                  (1 + ((NCDecomp.block tInners tTail).size - 1)) := by
              have hts := ht_sz
              simp [NCDecomp.size] at hts ⊢; omega
            have hneed₁ : bs.length ≥ inners.length + NCDecomp.sizeList inners := by omega
            obtain ⟨args, hgap1, hgap2⟩ := central_gaps_eq c inners bs hneed₁
            have hrem_len : (bs.drop (inners.length + NCDecomp.sizeList inners)).length ≥
                1 + ((NCDecomp.block tInners tTail).size - 1) := by
              rw [List.length_drop]; omega
            cases hdrop : bs.drop (inners.length + NCDecomp.sizeList inners) with
            | nil =>
                rw [hdrop] at hrem_len; simp at hrem_len
            | cons bSep bs₂ =>
                have hbs₂_len : bs₂.length ≥ (NCDecomp.block tInners tTail).size - 1 := by
                  rw [hdrop] at hrem_len; simp at hrem_len; omega
                have iht := central_stream_eq c (.block tInners tTail) bs₂ ht_sz hbs₂_len
                unfold evalNCStream
                rw [hgap1]
                dsimp
                rw [hdrop]
                dsimp
                change (let (tVal, bs₃) := evalNCStream (fun r a => listProd a * c (r + 1)) (.block tInners tTail) bs₂;
                  ((listProd args * c (inners.length + 1)) * bSep * tVal, bs₃)) = _
                rw [iht, hgap2]
                dsimp
                let m₁ := inners.length + NCDecomp.sizeList inners
                let m₂ := (NCDecomp.block tInners tTail).size - 1
                have hlt : (bs.take m₁).length = m₁ := List.length_take_of_le hneed₁
                have hbs_split : bs = bs.take m₁ ++ (bSep :: bs₂) := by
                  have hs := (List.take_append_drop m₁ bs).symm
                  dsimp [m₁] at hs ⊢
                  rw [hdrop] at hs; exact hs
                have htake_split : bs.take (m₁ + (1 + m₂)) =
                    bs.take m₁ ++ (bSep :: bs₂.take m₂) := by
                  conv => lhs; rw [hbs_split]
                  have heq : m₁ + (1 + m₂) = (bs.take m₁).length + (m₂ + 1) := by omega
                  rw [heq, take_append_exact]; rfl
                have hdrop_split : bs.drop (m₁ + (1 + m₂)) = bs₂.drop m₂ := by
                  conv => lhs; rw [hbs_split]
                  have heq : m₁ + (1 + m₂) = (bs.take m₁).length + (m₂ + 1) := by omega
                  rw [heq, drop_append_exact]; rfl
                rw [htot]
                change (((listProd (bs.take m₁) * blockWeightList c inners) * c (inners.length + 1)) * bSep *
                    (listProd (bs₂.take m₂) * blockWeightProd c (.block tInners tTail)),
                  bs₂.drop m₂) =
                  (listProd (bs.take (m₁ + (1 + m₂))) *
                    blockWeightProd c (.block inners (.block tInners tTail)),
                  bs.drop (m₁ + (1 + m₂)))
                rw [htake_split, hdrop_split]
                refine Prod.ext ?_ rfl
                rw [listProd_append, listProd]
                let P₁ := listProd (bs.take m₁)
                let W₁ := blockWeightList c inners
                let C₀ := c (inners.length + 1)
                let P₂ := listProd (bs₂.take m₂)
                let W₂ := blockWeightProd c (.block tInners tTail)
                change (((P₁ * W₁) * C₀) * bSep) * (P₂ * W₂) =
                  (P₁ * (bSep * P₂)) * ((C₀ * W₁) * W₂)
                rw [AssocRing.mul_assoc P₁ W₁ C₀, CommAssocRing.mul_comm W₁ C₀,
                    AssocRing.mul_assoc (P₁ * (C₀ * W₁)) bSep (P₂ * W₂),
                    ← AssocRing.mul_assoc bSep P₂ W₂,
                    AssocRing.mul_assoc P₁ (C₀ * W₁) (bSep * P₂ * W₂),
                    ← AssocRing.mul_assoc (C₀ * W₁) (bSep * P₂) W₂,
                    CommAssocRing.mul_comm (C₀ * W₁) (bSep * P₂),
                    AssocRing.mul_assoc (bSep * P₂) (C₀ * W₁) W₂,
                    ← AssocRing.mul_assoc P₁ (bSep * P₂) (C₀ * W₁ * W₂)]

  private theorem central_gaps_eq (c : Nat → B) :
      ∀ (inners : List NCDecomp) (bs : List B),
        bs.length ≥ inners.length + NCDecomp.sizeList inners →
        ∃ args : List B,
          evalGapsStream (fun r a => listProd a * c (r + 1)) inners bs =
            (args, bs.drop (inners.length + NCDecomp.sizeList inners)) ∧
          listProd args =
            listProd (bs.take (inners.length + NCDecomp.sizeList inners)) *
              blockWeightList c inners
    | [], bs, _ => by
        refine ⟨[], ?_, ?_⟩
        · simp [evalGapsStream, NCDecomp.sizeList]
        · simp [NCDecomp.sizeList, listProd, blockWeightList, one_mul_ring]
    | .nil :: rest, bs, hlen => by
        cases bs with
        | nil => simp [NCDecomp.sizeList] at hlen
        | cons b bs₁ =>
            have hlen₁ : bs₁.length ≥ rest.length + NCDecomp.sizeList rest := by
              simp [NCDecomp.sizeList, NCDecomp.size] at hlen; omega
            obtain ⟨restArgs, hrest1, hrest2⟩ := central_gaps_eq c rest bs₁ hlen₁
            have hcnt : (.nil :: rest).length + NCDecomp.sizeList (.nil :: rest) =
                (rest.length + NCDecomp.sizeList rest) + 1 := by
              simp [NCDecomp.sizeList, NCDecomp.size]; omega
            refine ⟨b :: restArgs, ?_, ?_⟩
            · change (let (ra, bs₂) := evalGapsStream (fun r a => listProd a * c (r + 1)) rest bs₁;
                (b :: ra, bs₂)) =
                (b :: restArgs, (b :: bs₁).drop ((.nil :: rest).length + NCDecomp.sizeList (.nil :: rest)))
              rw [hrest1, hcnt]; rfl
            · rw [hcnt]
              change b * listProd restArgs =
                (b * listProd (bs₁.take (rest.length + NCDecomp.sizeList rest))) *
                  (1 * blockWeightList c rest)
              rw [one_mul_ring, hrest2, AssocRing.mul_assoc]
    | .block pInners pTail :: rest, bs, hlen => by
        have hp_sz : (NCDecomp.block pInners pTail).size ≥ 1 := by
          simp [NCDecomp.size]; omega
        cases bs with
        | nil => simp [NCDecomp.sizeList] at hlen
        | cons bOpen bs₁ =>
            let mₚ := (NCDecomp.block pInners pTail).size - 1
            let mᵣ := rest.length + NCDecomp.sizeList rest
            have hcnt : (NCDecomp.block pInners pTail :: rest).length +
                NCDecomp.sizeList (NCDecomp.block pInners pTail :: rest) =
                (mₚ + (1 + mᵣ)) + 1 := by
              have hps := hp_sz
              dsimp [mₚ, mᵣ]
              simp [NCDecomp.sizeList, NCDecomp.size] at hps ⊢; omega
            have hlen₁ : bs₁.length ≥ mₚ + (1 + mᵣ) := by
              have hl : bs₁.length + 1 ≥
                  (NCDecomp.block pInners pTail :: rest).length +
                    NCDecomp.sizeList (NCDecomp.block pInners pTail :: rest) := hlen
              omega
            have ihp := central_stream_eq c (.block pInners pTail) bs₁ hp_sz (by omega)
            have hd_len : (bs₁.drop mₚ).length ≥ 1 + mᵣ := by
              rw [List.length_drop]; omega
            cases hdrop : bs₁.drop mₚ with
            | nil => rw [hdrop] at hd_len; simp at hd_len
            | cons bClose bs₃ =>
                have hbs₃_len : bs₃.length ≥ mᵣ := by
                  rw [hdrop] at hd_len; simp at hd_len; omega
                obtain ⟨restArgs, hrest1, hrest2⟩ := central_gaps_eq c rest bs₃ hbs₃_len
                let midVal := listProd (bs₁.take mₚ) * blockWeightProd c (.block pInners pTail)
                have hlt : (bs₁.take mₚ).length = mₚ := List.length_take_of_le (by omega)
                have hbs₁_split : bs₁ = bs₁.take mₚ ++ (bClose :: bs₃) := by
                  have hs := (List.take_append_drop mₚ bs₁).symm
                  rw [hdrop] at hs; exact hs
                refine ⟨(bOpen * midVal * bClose) :: restArgs, ?_, ?_⟩
                · change (let (mv, bs₂) := evalNCStream (fun r a => listProd a * c (r + 1)) (.block pInners pTail) bs₁;
                    match bs₂ with
                    | [] => ([], [])
                    | bCl :: bs₃' =>
                        let (ra, bs₄) := evalGapsStream (fun r a => listProd a * c (r + 1)) rest bs₃';
                        ((bOpen * mv * bCl) :: ra, bs₄)) = _
                  rw [ihp]
                  dsimp [mₚ] at hdrop ⊢
                  rw [hdrop]
                  dsimp
                  rw [hrest1]
                  change (bOpen * midVal * bClose :: restArgs, bs₃.drop mᵣ) =
                    (bOpen * midVal * bClose :: restArgs,
                     (bOpen :: bs₁).drop ((NCDecomp.block pInners pTail :: rest).length +
                       NCDecomp.sizeList (NCDecomp.block pInners pTail :: rest)))
                  rw [hcnt]
                  dsimp
                  refine Prod.ext rfl ?_
                  have hdrop_eq : bs₁.drop (mₚ + (1 + mᵣ)) = bs₃.drop mᵣ := by
                    conv => lhs; rw [hbs₁_split]
                    have heq : mₚ + (1 + mᵣ) = (bs₁.take mₚ).length + (mᵣ + 1) := by omega
                    rw [heq, drop_append_exact]; rfl
                  exact hdrop_eq.symm
                · rw [hcnt]
                  have htake_eq : bs₁.take (mₚ + (1 + mᵣ)) =
                      bs₁.take mₚ ++ (bClose :: bs₃.take mᵣ) := by
                    conv => lhs; rw [hbs₁_split]
                    have heq : mₚ + (1 + mᵣ) = (bs₁.take mₚ).length + (mᵣ + 1) := by omega
                    rw [heq, take_append_exact]; rfl
                  change (bOpen * midVal * bClose) * listProd restArgs =
                    (bOpen * listProd (bs₁.take (mₚ + (1 + mᵣ)))) *
                      (blockWeightProd c (.block pInners pTail) * blockWeightList c rest)
                  rw [htake_eq, listProd_append, listProd, hrest2]
                  dsimp [midVal, mᵣ]
                  rw [comm_rearrange_mid bOpen (listProd (bs₁.take mₚ))
                        (blockWeightProd c (.block pInners pTail)) bClose,
                      comm_rearrange_pair _ (blockWeightProd c (.block pInners pTail))
                        _ (blockWeightList c rest)]
                  simp [AssocRing.mul_assoc]
end

/-- Positive Central-Commutative Factorization Theorem. -/
theorem central_commutative_weighted_count (c : Nat → B) (π : NCDecomp) (bs : List B)
    (hsz : π.size ≥ 1) (hlen : bs.length = π.size - 1) :
    evalNC (fun r args => listProd args * c (r + 1)) π bs =
      listProd bs * blockWeightProd c π := by
  unfold evalNC
  rw [central_stream_eq c π bs hsz (by omega)]
  dsimp
  rw [← hlen, List.take_length]

end CentralCommutative

/-! ### 4. Universal Computability of Operator-Valued Polynomials of Degree ≤ 3 -/

inductive MonomDeg3 (B : Type u) where
  | deg0 (b₀ : B)
  | deg1 (v₁ : Bool) (b₀ b₁ : B)
  | deg2 (v₁ v₂ : Bool) (b₀ b₁ b₂ : B)
  | deg3 (v₁ v₂ v₃ : Bool) (b₀ b₁ b₂ b₃ : B)

abbrev PolyDeg3 (B : Type u) := List (MonomDeg3 B)

section PolyDeg3Eval
variable {A : Type u} {B : Type v} [AssocRing A] [AssocRing B]

def pickVar (X Y : A) : Bool → A
  | false => X
  | true  => Y

def evalMonomInA (S : OpValProbSpace A B) (X Y : A) : MonomDeg3 B → A
  | .deg0 b₀ => S.iota b₀
  | .deg1 v₁ b₀ b₁ => S.iota b₀ * pickVar X Y v₁ * S.iota b₁
  | .deg2 v₁ v₂ b₀ b₁ b₂ =>
      S.iota b₀ * (pickVar X Y v₁ * S.iota b₁ * pickVar X Y v₂) * S.iota b₂
  | .deg3 v₁ v₂ v₃ b₀ b₁ b₂ b₃ =>
      S.iota b₀ * (pickVar X Y v₁ * S.iota b₁ * pickVar X Y v₂ * S.iota b₂ * pickVar X Y v₃) * S.iota b₃

def evalPolyInA (S : OpValProbSpace A B) (X Y : A) : PolyDeg3 B → A
  | [] => 0
  | m :: ms => evalMonomInA S X Y m + evalPolyInA S X Y ms

structure MomentOracle3 (B : Type v) where
  mu1 : B
  mu2 : B → B
  mu3 : B → B → B

def oracleOfVar (S : OpValProbSpace A B) (Z : A) : MomentOracle3 B where
  mu1 := S.exp Z
  mu2 b₁ := S.exp (Z * S.iota b₁ * Z)
  mu3 b₁ b₂ := S.exp (Z * S.iota b₁ * Z * S.iota b₂ * Z)

def computeMonomDeg3 (oX oY : MomentOracle3 B) : MonomDeg3 B → B
  | .deg0 b₀ => b₀
  | .deg1 false b₀ b₁ => b₀ * oX.mu1 * b₁
  | .deg1 true  b₀ b₁ => b₀ * oY.mu1 * b₁
  | .deg2 false false b₀ b₁ b₂ => b₀ * oX.mu2 b₁ * b₂
  | .deg2 true  true  b₀ b₁ b₂ => b₀ * oY.mu2 b₁ * b₂
  | .deg2 false true  b₀ b₁ b₂ => b₀ * (oX.mu1 * b₁ * oY.mu1) * b₂
  | .deg2 true  false b₀ b₁ b₂ => b₀ * (oY.mu1 * b₁ * oX.mu1) * b₂
  | .deg3 false false false b₀ b₁ b₂ b₃ => b₀ * oX.mu3 b₁ b₂ * b₃
  | .deg3 true  true  true  b₀ b₁ b₂ b₃ => b₀ * oY.mu3 b₁ b₂ * b₃
  | .deg3 false false true  b₀ b₁ b₂ b₃ => b₀ * (oX.mu2 b₁ * b₂ * oY.mu1) * b₃
  | .deg3 true  true  false b₀ b₁ b₂ b₃ => b₀ * (oY.mu2 b₁ * b₂ * oX.mu1) * b₃
  | .deg3 false true  true  b₀ b₁ b₂ b₃ => b₀ * (oX.mu1 * b₁ * oY.mu2 b₂) * b₃
  | .deg3 true  false false b₀ b₁ b₂ b₃ => b₀ * (oY.mu1 * b₁ * oX.mu2 b₂) * b₃
  | .deg3 false true  false b₀ b₁ b₂ b₃ => b₀ * oX.mu2 (b₁ * oY.mu1 * b₂) * b₃
  | .deg3 true  false true  b₀ b₁ b₂ b₃ => b₀ * oY.mu2 (b₁ * oX.mu1 * b₂) * b₃

def computePolyDeg3 (oX oY : MomentOracle3 B) : PolyDeg3 B → B
  | [] => 0
  | m :: ms => computeMonomDeg3 oX oY m + computePolyDeg3 oX oY ms

theorem computeMonomDeg3_sound (S : OpValProbSpace A B) {P₀ P₁ : A → Prop}
    (hF : IsBFree S P₀ P₁) {X Y : A} (hX : P₀ X) (hY : P₁ Y) (m : MonomDeg3 B) :
    S.exp (evalMonomInA S X Y m) =
      computeMonomDeg3 (oracleOfVar S X) (oracleOfVar S Y) m := by
  cases m with
  | deg0 b₀ => exact S.exp_iota b₀
  | deg1 v₁ b₀ b₁ =>
      cases v₁ <;> exact S.exp_bimod b₀ b₁ _
  | deg2 v₁ v₂ b₀ b₁ b₂ =>
      cases v₁ <;> cases v₂
      · exact S.exp_bimod b₀ b₂ _
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_XY_bfree S hF hX hY b₁]; rfl
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_YX_bfree S hF hX hY b₁]; rfl
      · exact S.exp_bimod b₀ b₂ _
  | deg3 v₁ v₂ v₃ b₀ b₁ b₂ b₃ =>
      cases v₁ <;> cases v₂ <;> cases v₃
      · exact S.exp_bimod b₀ b₃ _
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_XXY_bfree S hF hX hY b₁ b₂]; rfl
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_XYX_bfree S hF hX hY b₁ b₂]; rfl
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_XYY_bfree S hF hX hY b₁ b₂]; rfl
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_YXX_bfree S hF hX hY b₁ b₂]; rfl
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_YXY_bfree S hF hX hY b₁ b₂]; rfl
      · rw [evalMonomInA, S.exp_bimod, pickVar, pickVar, exp_YYX_bfree S hF hX hY b₁ b₂]; rfl
      · exact S.exp_bimod b₀ b₃ _

theorem poly_deg_le_3_universal_soundness (S : OpValProbSpace A B) {P₀ P₁ : A → Prop}
    (hF : IsBFree S P₀ P₁) {X Y : A} (hX : P₀ X) (hY : P₁ Y) (P : PolyDeg3 B) :
    S.exp (evalPolyInA S X Y P) =
      computePolyDeg3 (oracleOfVar S X) (oracleOfVar S Y) P := by
  induction P with
  | nil => exact S.exp_zero
  | cons m ms ih =>
      simp only [evalPolyInA, computePolyDeg3, S.exp_add]
      rw [computeMonomDeg3_sound S hF hX hY m, ih]

end PolyDeg3Eval

/-! ### 5. Verification of Speicher's Nested Recursion Through Nesting Depth 3 (`n = 6`) -/

def semiCumulantOracle (η : Mat2 Int → Mat2 Int) : Nat → List (Mat2 Int) → Mat2 Int
  | 1, [b] => η b
  | _, _   => 0

set_option maxRecDepth 4000 in
theorem speicher_depth3_n6_verified :
    sumOverNC
      (semiCumulantOracle (fun B =>
        Mat2.sigmaX * B * Mat2.sigmaX + Mat2.E11 * B * Mat2.E11))
      6 [Mat2.I2, Mat2.I2, Mat2.I2, Mat2.I2, Mat2.I2] =
    mat2FockSpace.exp
      (ringPow (⟨0, FockOp.semiOp false, FockOp.semiOp false, 0⟩ +
                ⟨FockOp.semiOp true, 0, 0, 0⟩) 6) := by
  have lhs_eq :
      sumOverNC
        (semiCumulantOracle (fun B =>
          Mat2.sigmaX * B * Mat2.sigmaX + Mat2.E11 * B * Mat2.E11))
        6 [Mat2.I2, Mat2.I2, Mat2.I2, Mat2.I2, Mat2.I2] = Mat2.diagMat 30 12 := by
    apply Mat2.ext <;> rfl
  have rhs_eq :
      mat2FockSpace.exp
        (ringPow (⟨0, FockOp.semiOp false, FockOp.semiOp false, 0⟩ +
                  ⟨FockOp.semiOp true, 0, 0, 0⟩) 6) = Mat2.diagMat 30 12 := by
    apply Mat2.ext <;> rfl
  rw [lhs_eq, rhs_eq]

end Conjecture00000004759
