/-
  Conjecture 00000003970 — Verified Strict 32-Bit Native-GMP Subset-Convolution Evaluator,
  Direct `NatBST` Injectivity Map, Memoized Connectivity, and Concrete `detRows` Evaluator
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.CanonGraphs

namespace Conjecture00000003970

/-! ### Strict Call-By-Value `Nat` Combinator (`sNat`) -/

/-- Forces WHNF evaluation of `x : Nat` to a concrete GMP numeral before substituting into `k`,
    eliminating `let` zeta-duplication in `whnf` / `isDefEq`. -/
def sNat {α : Type u} (x : Nat) (k : Nat → α) : α :=
  match x with
  | 0 => k 0
  | n + 1 => k (Nat.succ n)

@[simp] theorem sNat_eq {α : Type u} (x : Nat) (k : Nat → α) : sNat x k = k x := by
  cases x <;> rfl

theorem nat_mod_eq_op (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_div_eq_op (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_add_eq_op (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub_eq_op (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul_eq_op (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_pow_eq_op (a b : Nat) : Nat.pow a b = a ^ b := rfl

theorem nat_beq_eq_beq (a b : Nat) : Nat.beq a b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [Nat.beq_refl]
  · have h1 : Nat.beq a b = false := Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)
    have h2 : (a == b) = false := Bool.eq_false_iff.mpr fun e => h (of_decide_eq_true (by simpa using e))
    rw [h1, h2]

/-! ### Part 1: Direct `NatBST` → `NatMapBST` Injectivity Verifier -/

inductive NatMapBST where
  | empty : NatMapBST
  | branch : Nat → Nat → NatMapBST → NatMapBST → NatMapBST

def nmLookup : NatMapBST → Nat → Option Nat
  | .empty, _ => none
  | .branch k v l r, q =>
    if Nat.beq q k then some v
    else if Nat.ble (Nat.succ q) k then nmLookup l q
    else nmLookup r q

def nmInsert : NatMapBST → Nat → Nat → Option NatMapBST
  | .empty, k, v => some (.branch k v .empty .empty)
  | .branch k₀ v₀ l r, k, v =>
    if Nat.beq k k₀ then
      if Nat.beq v v₀ then some (.branch k₀ v₀ l r) else none
    else if Nat.ble (Nat.succ k) k₀ then
      match nmInsert l k v with
      | none => none
      | some l' => some (.branch k₀ v₀ l' r)
    else
      match nmInsert r k v with
      | none => none
      | some r' => some (.branch k₀ v₀ l r')

def nmInsertBST (fn : Nat → Nat) : NatBST → NatMapBST → Option NatMapBST
  | .empty, acc => some acc
  | .branch m l r, acc =>
    sNat (fn m) fun k =>
      match nmInsert acc k m with
      | none => none
      | some acc1 =>
        match nmInsertBST fn l acc1 with
        | none => none
        | some acc2 => nmInsertBST fn r acc2

theorem nmLookup_nmInsert :
    ∀ {t t' : NatMapBST} {k v : Nat},
      nmInsert t k v = some t' →
      nmLookup t' k = some v ∧ (∀ q, q ≠ k → nmLookup t' q = nmLookup t q)
  | .empty, _, k, v, h => by
    injection h with h'; subst h'
    refine ⟨by simp [nmLookup], fun q hqk => ?_⟩
    have b : Nat.beq q k = false := Bool.eq_false_iff.mpr fun e => hqk (Nat.eq_of_beq_eq_true e)
    unfold nmLookup; simp only [b, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  | .branch k₀ v₀ l r, _, k, v, h => by
    unfold nmInsert at h
    by_cases hkk₀ : Nat.beq k k₀ = true
    · have hkeq : k = k₀ := Nat.eq_of_beq_eq_true hkk₀
      subst hkeq; simp only [Nat.beq_refl, ↓reduceIte] at h
      by_cases hvv₀ : Nat.beq v v₀ = true
      · have hveq : v = v₀ := Nat.eq_of_beq_eq_true hvv₀
        subst hveq; simp only [Nat.beq_refl, ↓reduceIte] at h
        injection h with h'; subst h'
        exact ⟨by simp [nmLookup], fun _ _ => rfl⟩
      · have hvvF := Bool.eq_false_iff.mpr hvv₀
        simp [hvvF] at h
    · have hkkF := Bool.eq_false_iff.mpr hkk₀
      simp only [hkkF, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hlt : Nat.ble (Nat.succ k) k₀ = true
      · simp only [hlt, ↓reduceIte] at h
        cases hins : nmInsert l k v with
        | none => rw [hins] at h; cases h
        | some l' =>
          rw [hins] at h; injection h with h'; subst h'
          rcases nmLookup_nmInsert hins with ⟨hl1, hl2⟩
          refine ⟨by simp [nmLookup, hkkF, hlt, hl1], fun q hqk => ?_⟩
          unfold nmLookup
          by_cases hqk₀ : Nat.beq q k₀ = true
          · simp [hqk₀]
          · have hqkF := Bool.eq_false_iff.mpr hqk₀
            simp only [hqkF, Bool.false_eq_true, ↓reduceIte]
            split
            · exact hl2 q hqk
            · rfl
      · have hltF := Bool.eq_false_iff.mpr hlt
        simp only [hltF, Bool.false_eq_true, ↓reduceIte] at h
        cases hins : nmInsert r k v with
        | none => rw [hins] at h; cases h
        | some r' =>
          rw [hins] at h; injection h with h'; subst h'
          rcases nmLookup_nmInsert hins with ⟨hr1, hr2⟩
          refine ⟨by simp [nmLookup, hkkF, hltF, hr1], fun q hqk => ?_⟩
          unfold nmLookup
          by_cases hqk₀ : Nat.beq q k₀ = true
          · simp [hqk₀]
          · have hqkF := Bool.eq_false_iff.mpr hqk₀
            simp only [hqkF, Bool.false_eq_true, ↓reduceIte]
            split
            · rfl
            · exact hr2 q hqk

theorem nmInsert_preserves_existing :
    ∀ {T T' : NatMapBST} {k v w : Nat},
      nmInsert T k v = some T' → nmLookup T k = some w → v = w
  | .empty, _, _, _, _, _, hlk0 => by cases hlk0
  | .branch k₀ _ l r, _, k, v, w, hi, hl0 => by
    unfold nmInsert at hi; unfold nmLookup at hl0
    by_cases hkk₀ : Nat.beq k k₀ = true
    · simp only [hkk₀, ↓reduceIte] at hi hl0
      injection hl0 with hw
      rw [hw] at hi
      by_cases hvv : Nat.beq v w = true
      · exact Nat.eq_of_beq_eq_true hvv
      · have hvvF := Bool.eq_false_iff.mpr hvv
        simp [hvvF] at hi
    · have hkkF := Bool.eq_false_iff.mpr hkk₀
      simp only [hkkF, Bool.false_eq_true, ↓reduceIte] at hi hl0
      split at hi
      · next hlt =>
        cases h1 : nmInsert l k v with
        | none => rw [h1] at hi; cases hi
        | some _ => simp only [hlt, ↓reduceIte] at hl0; exact nmInsert_preserves_existing h1 hl0
      · next hlt =>
        cases h1 : nmInsert r k v with
        | none => rw [h1] at hi; cases hi
        | some _ => simp only [hlt, ↓reduceIte] at hl0; exact nmInsert_preserves_existing h1 hl0

theorem nmInsertBST_lookup (fn : Nat → Nat) :
    ∀ (bst : NatBST) (acc res : NatMapBST),
      nmInsertBST fn bst acc = some res →
      ∀ m, (m ∈ bstToList bst ∨ nmLookup acc (fn m) = some m) →
        nmLookup res (fn m) = some m
  | .empty, _, _, h, _, hm => by
    injection h with h'; subst h'
    rcases hm with hmem | hlk
    · cases hmem
    · exact hlk
  | .branch v l r, acc, res, h, m, hm => by
    unfold nmInsertBST at h
    simp only [sNat_eq] at h
    cases h1 : nmInsert acc (fn v) v with
    | none => rw [h1] at h; cases h
    | some acc1 =>
      rw [h1] at h; dsimp only at h
      cases h2 : nmInsertBST fn l acc1 with
      | none => rw [h2] at h; cases h
      | some acc2 =>
        rw [h2] at h; dsimp only at h
        rcases nmLookup_nmInsert h1 with ⟨hv1, hv2⟩
        have hl := fun z hz => nmInsertBST_lookup fn l acc1 acc2 h2 z hz
        refine nmInsertBST_lookup fn r acc2 res h m ?_
        rcases hm with hmem | hlk
        · unfold bstToList at hmem
          rcases List.mem_cons.mp hmem with rfl | hlr
          · exact Or.inr (hl m (Or.inr hv1))
          · rcases List.mem_append.mp hlr with hml | hmr
            · exact Or.inr (hl m (Or.inl hml))
            · exact Or.inl hmr
        · by_cases hfv : fn m = fn v
          · right
            have hvm : v = m := nmInsert_preserves_existing h1 (hfv ▸ hlk)
            subst hvm
            exact hl v (Or.inr hv1)
          · exact Or.inr (hl m (Or.inr ((hv2 (fn m) hfv).trans hlk)))

theorem nmInsertBST_sound {fn : Nat → Nat} {bst : NatBST}
    (hok : (nmInsertBST fn bst .empty).isSome = true) :
    ∀ m₁ ∈ bstToList bst, ∀ m₂ ∈ bstToList bst, fn m₁ = fn m₂ → m₁ = m₂ := by
  cases hall : nmInsertBST fn bst .empty with
  | none => rw [hall] at hok; cases hok
  | some tFinal =>
    intro m₁ hm₁ m₂ hm₂ hfeq
    have h1 := nmInsertBST_lookup fn bst .empty tFinal hall m₁ (Or.inl hm₁)
    have h2 := nmInsertBST_lookup fn bst .empty tFinal hall m₂ (Or.inl hm₂)
    rw [hfeq, h2] at h1
    injection h1 with h12
    exact h12.symm

/-! ### Part 2: Native-GMP Bit Queries & Memoized Reachability -/

def fastTestBit (m k : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div m (Nat.pow 2 k)) 2) 1

theorem fastTestBit_eq (m k : Nat) : fastTestBit m k = testBitNat m k := by
  unfold fastTestBit testBitNat
  simp only [nat_beq_eq_beq, nat_mod_eq_op, nat_div_eq_op, nat_pow_eq_op]
  rw [Nat.shiftRight_eq_div_pow]
  change (((m / 2 ^ k) % 2) == 1) = (((m / 2 ^ k) &&& 1) == 1)
  rw [and_one_eq_mod_two]

def fastHasMaskEdge (n mask u v : Nat) : Bool :=
  !(Nat.beq u v) && (fastTestBit mask (Nat.add (Nat.mul u n) v) || fastTestBit mask (Nat.add (Nat.mul v n) u))

theorem fastHasMaskEdge_eq (n mask u v : Nat) :
    fastHasMaskEdge n mask u v = hasMaskEdge n mask u v := by
  unfold fastHasMaskEdge hasMaskEdge
  simp only [nat_beq_eq_beq, nat_add_eq_op, nat_mul_eq_op, fastTestBit_eq]

def memoizeFinBool {n : Nat} (R : Fin n → Bool) : Nat :=
  packBools ((List.range n).map (fun k => if hk : k < n then R ⟨k, hk⟩ else false))

theorem fastTestBit_memoizeFinBool {n : Nat} (R : Fin n → Bool) (x : Fin n) :
    fastTestBit (memoizeFinBool R) x.val = R x := by
  rw [fastTestBit_eq]
  unfold memoizeFinBool
  rw [testBitNat_packBools _ x.val (by simp [x.isLt])]
  simp [x.isLt]

def stepReachMask (n : Nat) (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) (rm : Nat) : Nat :=
  memoizeFinBool (stepReachBack adj S (fun y => fastTestBit rm y.val))

def iterReachMask (n : Nat) (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) : Nat → Nat → Nat
  | 0, rm => rm
  | k + 1, rm => sNat rm fun rmv => iterReachMask n adj S k (stepReachMask n adj S rmv)

theorem fastTestBit_iterReachMask {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    ∀ (k : Nat) (R : Fin n → Bool) (u : Fin n),
      fastTestBit (iterReachMask n adj S k (memoizeFinBool R)) u.val =
        iterReachBack adj S k R u
  | 0, R, u => fastTestBit_memoizeFinBool R u
  | k + 1, R, u => by
    unfold iterReachMask
    simp only [sNat_eq]
    unfold stepReachMask
    have hfun : (fun y : Fin n => fastTestBit (memoizeFinBool R) y.val) = R :=
      funext (fastTestBit_memoizeFinBool R)
    rw [hfun]
    exact fastTestBit_iterReachMask adj S k (stepReachBack adj S R) u

def findFirst {α : Type u} (P : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if P x then some x else findFirst P xs

theorem findFirst_some {α : Type u} {P : α → Bool} :
    ∀ {L : List α} {w : α}, findFirst P L = some w → P w = true
  | [], _, h => by cases h
  | x :: _, w, h => by
    unfold findFirst at h
    by_cases hx : P x = true
    · simp only [hx, ↓reduceIte] at h
      injection h with h'; subst h'; exact hx
    · have hxf := Bool.eq_false_iff.mpr hx
      simp only [hxf, Bool.false_eq_true, ↓reduceIte] at h
      exact findFirst_some h

theorem findFirst_none {α : Type u} {P : α → Bool} :
    ∀ {L : List α}, findFirst P L = none → ∀ x ∈ L, P x = false
  | [], _, _, hx => by cases hx
  | y :: _, h, x, hx => by
    unfold findFirst at h
    by_cases hy : P y = true
    · simp [hy] at h
    · have hyf := Bool.eq_false_iff.mpr hy
      simp only [hyf, Bool.false_eq_true, ↓reduceIte] at h
      rcases List.mem_cons.mp hx with rfl | hys
      · exact hyf
      · exact findFirst_none h x hys

def fastIsConnSubgraph {n : Nat} (G : SimpleGraphN n) (S : Fin n → Bool) : Bool :=
  match findFirst S (allFin n) with
  | none => false
  | some w₀ =>
    sNat (iterReachMask n G.adj S n (memoizeFinBool (fun x => S w₀ && decide (x = w₀)))) fun rm =>
      (allFin n).all (fun u => !S u || fastTestBit rm u.val)

theorem fastIsConnSubgraph_eq {n : Nat} (G : SimpleGraphN n) (S : Fin n → Bool) :
    fastIsConnSubgraph G S = isConnectedSubgraphBool G.adj S := by
  by_cases hc : IsConnectedSubgraph G.adj S
  · have hrhs : isConnectedSubgraphBool G.adj S = true :=
      (isConnectedSubgraphBool_eq_true_iff G.adj S).mpr hc
    rw [hrhs]
    unfold fastIsConnSubgraph
    cases hf : findFirst S (allFin n) with
    | none =>
      rcases hc with ⟨⟨u₀, hu₀⟩, _⟩
      have hf0 := findFirst_none hf u₀ (mem_allFin u₀)
      rw [hu₀] at hf0; cases hf0
    | some w₀ =>
      dsimp only
      simp only [sNat_eq]
      have hw₀ : S w₀ = true := findFirst_some hf
      apply List.all_eq_true.mpr; intro u _
      cases hSu : S u
      · simp
      · simp only [Bool.not_true, Bool.false_or]
        rw [fastTestBit_iterReachMask]
        exact (reachBool_eq_true_iff G.adj S u w₀).mpr (hc.2 u w₀ hSu hw₀)
  · have hrhs : isConnectedSubgraphBool G.adj S = false :=
      Bool.eq_false_iff.mpr fun h => hc ((isConnectedSubgraphBool_eq_true_iff G.adj S).mp h)
    rw [hrhs]
    apply Bool.eq_false_iff.mpr; intro hlhs
    apply hc
    unfold fastIsConnSubgraph at hlhs
    cases hf : findFirst S (allFin n) with
    | none => rw [hf] at hlhs; cases hlhs
    | some w₀ =>
      rw [hf] at hlhs; dsimp only at hlhs; simp only [sNat_eq] at hlhs
      have hw₀ : S w₀ = true := findFirst_some hf
      have hreach : ∀ u : Fin n, S u = true → ReachableIn G.adj S u w₀ := by
        intro u hSu
        have hu := List.all_eq_true.mp hlhs u (mem_allFin u)
        simp only [hSu, Bool.not_true, Bool.false_or] at hu
        rw [fastTestBit_iterReachMask] at hu
        exact (reachBool_eq_true_iff G.adj S u w₀).mp hu
      exact ⟨⟨w₀, hw₀⟩, fun u v hSu hSv =>
        (hreach u hSu).trans (ReachableIn.symm_of_symm G.symm (hreach v hSv))⟩

def fastIsConnectedGraph {n : Nat} (G : SimpleGraphN n) : Bool :=
  fastIsConnSubgraph G (fun _ => true)

theorem isConnectedGraph_iff_fast {n : Nat} (G : SimpleGraphN n) :
    IsConnectedGraph G ↔ fastIsConnectedGraph G = true := by
  unfold IsConnectedGraph fastIsConnectedGraph
  rw [fastIsConnSubgraph_eq, isConnectedSubgraphBool_eq_true_iff]

/-! ### Part 3: Strict 32-Bit Lane Native-GMP Evaluator (`sNat` + Direct `Nat.*`) -/

/-- 32-bit tree lane modulus `2^32 = 4294967296` (since `2^(8*7/2) = 2^28 < 2^32`). -/
def base32Mod : Nat := 4294967296

theorem base32Mod_eq : base32Mod = 2 ^ 32 := by decide

/-- 40-bit output vector lane modulus `2^40 = 1099511627776` (since `2^28 * 2^8 = 2^36 < 2^40`). -/
def vecMod40 : Nat := 1099511627776

theorem vecMod40_eq : vecMod40 = 2 ^ 40 := by decide

theorem vecMod40_pos : 0 < vecMod40 := by decide

def laneMod : Nat → Nat
  | 0 => 4294967296
  | 1 => 18446744073709551616
  | 2 => 340282366920938463463374607431768211456
  | 3 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | 4 => 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
  | 5 => 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216
  | 6 => 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521914333389668342420684974786564569494856176035326322058077805659331026192708460314150258592864177116725943603718461857357598351152301645904403697613233287231227125684710820209725157101726931323469678542580656697935045997268352998638215525166389437335543602135433229604645318478604952148193555853611059596230656
  | 7 => 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848826811934997558340890106714439262837987573438185793607263236087851365277945956976543709998340361590134383718314428070011855946226376318839397712745672334684344586617496807908705803704071284048740118609114467977783598029006686938976881787785946905630190260940599579453432823469303026696443059025015972399867714215541693835559885291486318237914434496734087811872639496475100189041349008417061675093668333850551032972088269550769983616369411933015213796825837188091833656751221318492846368125550225998300412344784862595674492194617023806505913245610825731835380087608622102834270197698202313169017678006675195485079921636419370285375124784014907159135459982790513399611551794271106831134090584272884279791554849782954323534517065223269061394905987693002122963395687782878948440616007412945674919823050571642377154816321380631045902916136926708342856440730447899971901781465763473223850267253059899795996090799469201774624817718449867455659250178329070473119433165550807568221846571746373296884912819520317457002440926616910874148385078411929804522981857338977648103126085903001302413467189726673216491511131602920781738033436090243804708340403154190336
  | k + 8 =>
    sNat (laneMod (k + 7)) fun m => Nat.mul m m

theorem pow2_pos (w : Nat) : 0 < 2 ^ w := by
  induction w with
  | zero => omega
  | succ _ ih => rw [Nat.pow_succ]; omega

theorem laneMod_zero : laneMod 0 = base32Mod := rfl

theorem laneMod_succ (k : Nat) : laneMod (k + 1) = laneMod k * laneMod k := by
  match k with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide
  | 4 => decide | 5 => decide | 6 => decide | 7 => decide
  | k' + 8 =>
    show sNat (laneMod (k' + 8)) (fun m => Nat.mul m m) = laneMod (k' + 8) * laneMod (k' + 8)
    simp only [sNat_eq, nat_mul_eq_op]

theorem laneMod_pos : ∀ (k : Nat), 0 < laneMod k
  | 0 => by decide
  | k + 1 => by
    rw [laneMod_succ]
    exact Nat.mul_pos (laneMod_pos k) (laneMod_pos k)

def packedScaleMask32 (n mask top : Nat) : (k : Nat) → Nat → Nat
  | 0, x => x
  | k + 1, p =>
    sNat p fun pv =>
      let m := laneMod k
      sNat (packedScaleMask32 n mask top k (Nat.mod pv m)) fun l =>
        sNat (packedScaleMask32 n mask top k (Nat.div pv m)) fun r =>
          let r' := if fastHasMaskEdge n mask k top then Nat.add r r else r
          Nat.add l (Nat.mul m r')

def packedBuildPow2_32 (n mask : Nat) : (k : Nat) → Nat
  | 0 => 1
  | k + 1 =>
    sNat (packedBuildPow2_32 n mask k) fun prev =>
      sNat (packedScaleMask32 n mask k k prev) fun p1 =>
        Nat.add prev (Nat.mul (laneMod k) p1)

def packedSubsetConv32 : (k : Nat) → Nat → Nat → Nat
  | 0, a, b => Nat.mul a b
  | k + 1, f, g =>
    sNat f fun fv =>
      sNat g fun gv =>
        let m := laneMod k
        sNat (Nat.mod fv m) fun f0 =>
          sNat (Nat.div fv m) fun f1 =>
            sNat (Nat.mod gv m) fun g0 =>
              sNat (Nat.div gv m) fun g1 =>
                Nat.add (packedSubsetConv32 k f0 g0)
                  (Nat.mul m (Nat.add (packedSubsetConv32 k f0 g1) (packedSubsetConv32 k f1 g0)))

def packedSolveConn32 : (k : Nat) → Nat → Nat → Nat
  | 0, _, p1 => p1
  | k + 1, p0, p1 =>
    sNat p0 fun p0v =>
      sNat p1 fun p1v =>
        let m := laneMod k
        sNat (Nat.mod p0v m) fun p00 =>
          sNat (Nat.div p0v m) fun p01 =>
            sNat (Nat.mod p1v m) fun p10 =>
              sNat (Nat.div p1v m) fun p11 =>
                sNat (packedSolveConn32 k p00 p10) fun c10 =>
                  sNat (Nat.sub p11 (packedSubsetConv32 k c10 p01)) fun rem =>
                    sNat (packedSolveConn32 k p00 rem) fun c11 =>
                      Nat.add c10 (Nat.mul m c11)

def packedAllConn32 : (n : Nat) → Nat → Nat
  | 0, _ => 0
  | k + 1, p =>
    sNat p fun pv =>
      let m := laneMod k
      sNat (Nat.mod pv m) fun p0 =>
        sNat (Nat.div pv m) fun p1 =>
          Nat.add (packedAllConn32 k p0) (Nat.mul m (packedSolveConn32 k p0 p1))

def packedSumByOrder32 : (n : Nat) → Nat → Nat
  | 0, x => x
  | k + 1, p =>
    sNat p fun pv =>
      let m := laneMod k
      sNat (packedSumByOrder32 k (Nat.mod pv m)) fun sl =>
        sNat (packedSumByOrder32 k (Nat.div pv m)) fun sr =>
          Nat.add sl (Nat.mul vecMod40 sr)

def fastConnEdgeKey32 (n mask : Nat) : Nat :=
  sNat (packedBuildPow2_32 n mask n) fun b =>
    sNat (packedAllConn32 n b) fun c =>
      Nat.div (packedSumByOrder32 n c) vecMod40

def fastAllEdgeKey32 (n mask : Nat) : Nat :=
  sNat (packedBuildPow2_32 n mask n) fun b =>
    Nat.div (packedSumByOrder32 n b) vecMod40

/-! #### 32-Bit Tree Encoding & Correctness Proofs -/

def treeAllLt (B : Nat) : {k : Nat} → BTree Nat k → Prop
  | _, .leaf x => x < B
  | _, .node l r => treeAllLt B l ∧ treeAllLt B r

def treeLe : {k : Nat} → BTree Nat k → BTree Nat k → Prop
  | _, .leaf a, .leaf b => a ≤ b
  | _, .node l₁ r₁, .node l₂ r₂ => treeLe l₁ l₂ ∧ treeLe r₁ r₂

@[simp] theorem treeAllLt_leaf (B x : Nat) : treeAllLt B (.leaf x) = (x < B) := rfl
@[simp] theorem treeAllLt_node (B : Nat) {k : Nat} (l r : BTree Nat k) :
    treeAllLt B (.node l r) = (treeAllLt B l ∧ treeAllLt B r) := rfl
@[simp] theorem treeLe_leaf (a b : Nat) : treeLe (.leaf a) (.leaf b) = (a ≤ b) := rfl
@[simp] theorem treeLe_node {k : Nat} (l₁ r₁ l₂ r₂ : BTree Nat k) :
    treeLe (.node l₁ r₁) (.node l₂ r₂) = (treeLe l₁ l₂ ∧ treeLe r₁ r₂) := rfl

@[simp] theorem btreeMap2_leaf {α β γ} (fn : α → β → γ) (a : α) (b : β) :
    btreeMap2 fn (.leaf a) (.leaf b) = .leaf (fn a b) := rfl
@[simp] theorem btreeMap2_node {α β γ} {k : Nat} (fn : α → β → γ)
    (l₁ r₁ : BTree α k) (l₂ r₂ : BTree β k) :
    btreeMap2 fn (.node l₁ r₁) (.node l₂ r₂) = .node (btreeMap2 fn l₁ l₂) (btreeMap2 fn r₁ r₂) := rfl

def packTree32 : {k : Nat} → BTree Nat k → Nat
  | 0, .leaf x => x
  | k + 1, .node l r => packTree32 l + laneMod k * packTree32 r

@[simp] theorem packTree32_leaf (x : Nat) : packTree32 (.leaf x) = x := rfl
@[simp] theorem packTree32_node {k : Nat} (l r : BTree Nat k) :
    packTree32 (.node l r) = packTree32 l + laneMod k * packTree32 r := rfl

theorem treeAllLt_of_le {B₁ B₂ : Nat} (hB : B₁ ≤ B₂) :
    ∀ {k : Nat} {T : BTree Nat k}, treeAllLt B₁ T → treeAllLt B₂ T
  | 0, .leaf _, hx => Nat.lt_of_lt_of_le hx hB
  | _ + 1, .node _ _, h => ⟨treeAllLt_of_le hB h.1, treeAllLt_of_le hB h.2⟩

theorem treeAllLt_mono {B : Nat} :
    ∀ {k : Nat} {T₁ T₂ : BTree Nat k}, treeLe T₁ T₂ → treeAllLt B T₂ → treeAllLt B T₁
  | 0, .leaf _, .leaf _, hle, hlt => Nat.lt_of_le_of_lt hle hlt
  | _ + 1, .node _ _, .node _ _, h1, h2 =>
    ⟨treeAllLt_mono h1.1 h2.1, treeAllLt_mono h1.2 h2.2⟩

theorem packTree32_lt :
    ∀ {k : Nat} (T : BTree Nat k),
      treeAllLt base32Mod T → packTree32 T < laneMod k
  | 0, .leaf _ => fun hx => by
    simp only [packTree32_leaf, treeAllLt_leaf, laneMod_zero] at *
    exact hx
  | k + 1, .node l r => fun h => by
    rw [packTree32_node, laneMod_succ]
    have ihL := packTree32_lt l h.1
    have ihR := packTree32_lt r h.2
    have h1 : laneMod k * (packTree32 r + 1) ≤ laneMod k * laneMod k :=
      Nat.mul_le_mul_left (laneMod k) (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega

theorem split32_lo {k L R : Nat} (hL : L < laneMod k) :
    (L + laneMod k * R) % laneMod k = L := by
  rw [Nat.add_comm L _, Nat.mul_add_mod, Nat.mod_eq_of_lt hL]

theorem split32_hi {k L R : Nat} (hL : L < laneMod k) :
    (L + laneMod k * R) / laneMod k = R := by
  rw [Nat.add_comm L _, Nat.mul_add_div (laneMod_pos k), Nat.div_eq_of_lt hL, Nat.add_zero]

theorem packTree32_add :
    ∀ {k : Nat} (A B : BTree Nat k),
      packTree32 (btreeMap2 (· + ·) A B) = packTree32 A + packTree32 B
  | 0, .leaf _, .leaf _ => rfl
  | _ + 1, .node a0 a1, .node b0 b1 => by
    rw [btreeMap2_node, packTree32_node, packTree32_node, packTree32_node,
        packTree32_add a0 b0, packTree32_add a1 b1, Nat.mul_add]
    omega

theorem btreeMap2_sub_add :
    ∀ {k : Nat} {A B : BTree Nat k},
      treeLe B A → btreeMap2 (· + ·) (btreeMap2 (· - ·) A B) B = A
  | 0, .leaf a, .leaf b => fun hle => by
    simp only [treeLe_leaf] at hle
    simp only [btreeMap2_leaf]
    congr 1; omega
  | _ + 1, .node _ _, .node _ _ => fun h => by
    simp only [btreeMap2_node]
    rw [btreeMap2_sub_add h.1, btreeMap2_sub_add h.2]

theorem packTree32_sub {k : Nat} {A B : BTree Nat k} (hle : treeLe B A) :
    packTree32 (btreeMap2 (· - ·) A B) = packTree32 A - packTree32 B := by
  have h := congrArg packTree32 (btreeMap2_sub_add hle)
  rw [packTree32_add] at h
  omega

def triBound : Nat → Nat
  | 0 => 1
  | k + 1 => triBound k + k

theorem triBound_le_29 {r : Nat} (hr : r ≤ 8) : triBound r ≤ 29 ∧ triBound r + r ≤ 37 := by
  match r with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide
  | _ + 9 => omega

theorem treeAllLt_double :
    ∀ {k : Nat} {T : BTree Nat k} {B : Nat},
      treeAllLt B T → treeAllLt (B * 2) (btreeMap2 (· + ·) T T)
  | 0, .leaf _, _ => fun hx => by
    simp only [treeAllLt_leaf, btreeMap2_leaf] at *
    omega
  | _ + 1, .node _ _, _ => fun h => ⟨treeAllLt_double h.1, treeAllLt_double h.2⟩

theorem treeAllLt_scaleByNeighbors :
    ∀ {k : Nat} (row : Fin k → Bool) (T : BTree Nat k) {B : Nat},
      treeAllLt B T → treeAllLt (B * 2 ^ k) (scaleByNeighbors row T)
  | 0, _, .leaf _, _ => fun hx => by simpa [scaleByNeighbors] using hx
  | k + 1, row, .node l r, B => fun h => by
    unfold scaleByNeighbors
    simp only [treeAllLt_node]
    have ihl := treeAllLt_scaleByNeighbors (fun i => row i.castSucc) l h.1
    have ihr := treeAllLt_scaleByNeighbors (fun i => row i.castSucc) r h.2
    have hpow : B * 2 ^ (k + 1) = B * 2 ^ k * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have hleB : B * 2 ^ k ≤ B * 2 ^ (k + 1) :=
      Nat.mul_le_mul_left B (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨treeAllLt_of_le hleB ihl, ?_⟩
    split
    · rw [hpow]; exact treeAllLt_double ihr
    · exact treeAllLt_of_le hleB ihr

theorem treeAllLt_buildPow2Tree :
    ∀ (r : Nat) (adj : Fin r → Fin r → Bool),
      treeAllLt (2 ^ triBound r) (buildPow2Tree r adj)
  | 0, _ => by simp [buildPow2Tree, triBound]
  | k + 1, adj => by
    unfold buildPow2Tree
    simp only [treeAllLt_node]
    have ih := treeAllLt_buildPow2Tree k (fun i j => adj i.castSucc j.castSucc)
    have hsc := treeAllLt_scaleByNeighbors (fun i => adj i.castSucc (.last k)) _ ih
    have hpow : 2 ^ triBound k * 2 ^ k = 2 ^ triBound (k + 1) := by
      rw [← Nat.pow_add]; rfl
    rw [hpow] at hsc
    have hle : 2 ^ triBound k ≤ 2 ^ triBound (k + 1) :=
      Nat.pow_le_pow_right (by omega) (by simp only [triBound]; omega)
    exact ⟨treeAllLt_of_le hle ih, hsc⟩

theorem treeAllLt_buildPow2Tree_32 {r : Nat} (hr : r ≤ 8) (adj : Fin r → Fin r → Bool) :
    treeAllLt base32Mod (buildPow2Tree r adj) := by
  have h29 := (triBound_le_29 hr).1
  have hle : 2 ^ triBound r ≤ base32Mod := by
    rw [base32Mod_eq]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact treeAllLt_of_le hle (treeAllLt_buildPow2Tree r adj)

theorem packedScaleMask32_eq (n mask top : Nat) :
    ∀ (k : Nat) (T : BTree Nat k),
      treeAllLt base32Mod T →
      packedScaleMask32 n mask top k (packTree32 T) =
        packTree32 (scaleByNeighbors (fun i : Fin k => hasMaskEdge n mask i.val top) T)
  | 0, .leaf _ => fun _ => rfl
  | k + 1, .node l r => fun h => by
    unfold packedScaleMask32 scaleByNeighbors
    simp only [sNat_eq, packTree32_node, nat_add_eq_op, nat_mul_eq_op, nat_mod_eq_op, nat_div_eq_op]
    have hL_lt := packTree32_lt l h.1
    rw [split32_lo hL_lt, split32_hi hL_lt, fastHasMaskEdge_eq]
    have hcast : (fun i : Fin k => hasMaskEdge n mask i.castSucc.val top) =
        (fun i : Fin k => hasMaskEdge n mask i.val top) := rfl
    have hlast : hasMaskEdge n mask (Fin.last k).val top = hasMaskEdge n mask k top := rfl
    rw [hcast, hlast, packedScaleMask32_eq n mask top k l h.1,
        packedScaleMask32_eq n mask top k r h.2]
    cases hasMaskEdge n mask k top
    · simp
    · simp [packTree32_add]

theorem packedBuildPow2_32_eq (n mask : Nat) :
    ∀ (r : Nat), r ≤ 8 →
      packedBuildPow2_32 n mask r =
        packTree32 (buildPow2Tree r (fun i j : Fin r => hasMaskEdge n mask i.val j.val))
  | 0, _ => rfl
  | k + 1, hr => by
    unfold packedBuildPow2_32 buildPow2Tree
    simp only [sNat_eq, packTree32_node, nat_add_eq_op, nat_mul_eq_op]
    have hk : k ≤ 8 := by omega
    have hprev_lt := treeAllLt_buildPow2Tree_32 hk (fun i j : Fin k => hasMaskEdge n mask i.val j.val)
    have hcast : (fun i j : Fin k => hasMaskEdge n mask i.castSucc.val j.castSucc.val) =
        (fun i j : Fin k => hasMaskEdge n mask i.val j.val) := rfl
    have hlast : (fun i : Fin k => hasMaskEdge n mask i.castSucc.val (Fin.last k).val) =
        (fun i : Fin k => hasMaskEdge n mask i.val k) := rfl
    rw [hcast, hlast, packedBuildPow2_32_eq n mask k hk,
        packedScaleMask32_eq n mask k k _ hprev_lt]

theorem treeLe_add_left : ∀ {k : Nat} (A B : BTree Nat k), treeLe A (btreeMap2 (· + ·) A B)
  | 0, .leaf a, .leaf b => by show a ≤ a + b; omega
  | _ + 1, .node a0 a1, .node b0 b1 =>
    show treeLe a0 _ ∧ treeLe a1 _ from ⟨treeLe_add_left a0 b0, treeLe_add_left a1 b1⟩

theorem treeLe_add_right : ∀ {k : Nat} (A B : BTree Nat k), treeLe B (btreeMap2 (· + ·) A B)
  | 0, .leaf a, .leaf b => by show b ≤ a + b; omega
  | _ + 1, .node a0 a1, .node b0 b1 =>
    show treeLe b0 _ ∧ treeLe b1 _ from ⟨treeLe_add_right a0 b0, treeLe_add_right a1 b1⟩

theorem treeLe_trans : ∀ {k : Nat} {A B C : BTree Nat k}, treeLe A B → treeLe B C → treeLe A C
  | 0, .leaf _, .leaf _, .leaf _, h1, h2 => Nat.le_trans h1 h2
  | _ + 1, .node _ _, .node _ _, .node _ _, h1, h2 =>
    ⟨treeLe_trans h1.1 h2.1, treeLe_trans h1.2 h2.2⟩

theorem treeLe_of_subsetConv :
    ∀ {k : Nat} {C P₀ P₁ : BTree Nat k},
      leftmostLeaf P₀ = 1 → subsetConv C P₀ = P₁ → treeLe C P₁
  | 0, .leaf c, .leaf p0, .leaf p1, h1, hconv => by
    unfold leftmostLeaf at h1; subst h1
    unfold subsetConv at hconv; injection hconv with hcp
    show c ≤ p1; omega
  | k + 1, .node c0 c1, .node p00 p01, .node p10 p11, h1, hconv => by
    have h1' : leftmostLeaf p00 = 1 := h1
    have hl : subsetConv c0 p00 = p10 := congrArg btreeLeft hconv
    have hr : btreeMap2 (· + ·) (subsetConv c0 p01) (subsetConv c1 p00) = p11 :=
      congrArg btreeRight hconv
    show treeLe c0 p10 ∧ treeLe c1 p11
    refine ⟨treeLe_of_subsetConv h1' hl, ?_⟩
    have h1'' : treeLe c1 (subsetConv c1 p00) :=
      @treeLe_of_subsetConv k c1 p00 (subsetConv c1 p00) h1' rfl
    have h2'' : treeLe (subsetConv c1 p00) p11 :=
      hr ▸ treeLe_add_right (subsetConv c0 p01) (subsetConv c1 p00)
    exact treeLe_trans h1'' h2''

theorem packedSubsetConv32_eq :
    ∀ (k : Nat) (A B : BTree Nat k),
      treeAllLt base32Mod A → treeAllLt base32Mod B →
      packedSubsetConv32 k (packTree32 A) (packTree32 B) = packTree32 (subsetConv A B) := by
  intro k
  induction k with
  | zero =>
    intro A B _ _
    cases A; cases B
    rfl
  | succ k ih =>
    intro A B ha hb
    cases A with | node a0 a1 =>
    cases B with | node b0 b1 =>
    unfold packedSubsetConv32 subsetConv
    simp only [sNat_eq, packTree32_node, nat_add_eq_op, nat_mul_eq_op, nat_mod_eq_op, nat_div_eq_op]
    have hla := packTree32_lt a0 ha.1
    have hlb := packTree32_lt b0 hb.1
    rw [split32_lo hla, split32_hi hla, split32_lo hlb, split32_hi hlb,
        ih a0 b0 ha.1 hb.1,
        ih a0 b1 ha.1 hb.2,
        ih a1 b0 ha.2 hb.1,
        packTree32_add]

theorem packedSolveConn32_eq :
    ∀ (k : Nat) (C P₀ P₁ : BTree Nat k),
      leftmostLeaf P₀ = 1 → subsetConv C P₀ = P₁ →
      treeAllLt base32Mod P₀ → treeAllLt base32Mod P₁ →
      packedSolveConn32 k (packTree32 P₀) (packTree32 P₁) = packTree32 C := by
  intro k
  induction k with
  | zero =>
    intro C P₀ P₁ h1 hconv _ _
    cases C with | leaf c =>
    cases P₀ with | leaf p0 =>
    cases P₁ with | leaf p1 =>
    unfold leftmostLeaf at h1; subst h1
    unfold subsetConv at hconv; injection hconv with hcp
    change p1 = c
    omega
  | succ k ih =>
    intro C P₀ P₁ h1 hconv hp0 hp1
    cases C with | node c0 c1 =>
    cases P₀ with | node p00 p01 =>
    cases P₁ with | node p10 p11 =>
    unfold packedSolveConn32
    simp only [sNat_eq, packTree32_node, nat_add_eq_op, nat_mul_eq_op, nat_sub_eq_op, nat_mod_eq_op, nat_div_eq_op]
    have h1' : leftmostLeaf p00 = 1 := h1
    have hleft : subsetConv c0 p00 = p10 := congrArg btreeLeft hconv
    have hright : btreeMap2 (· + ·) (subsetConv c0 p01) (subsetConv c1 p00) = p11 :=
      congrArg btreeRight hconv
    have hlp0 := packTree32_lt p00 hp0.1
    have hlp1 := packTree32_lt p10 hp1.1
    rw [split32_lo hlp0, split32_hi hlp0, split32_lo hlp1, split32_hi hlp1]
    have ih0 := ih c0 p00 p10 h1' hleft hp0.1 hp1.1
    rw [ih0]
    have hc0_le : treeLe c0 p10 := treeLe_of_subsetConv h1' hleft
    have hc0_lt : treeAllLt base32Mod c0 := treeAllLt_mono hc0_le hp1.1
    rw [packedSubsetConv32_eq k c0 p01 hc0_lt hp0.2]
    have hconv_le : treeLe (subsetConv c0 p01) p11 :=
      hright ▸ treeLe_add_left (subsetConv c0 p01) (subsetConv c1 p00)
    rw [← packTree32_sub hconv_le]
    have hrem_eq : btreeMap2 (· - ·) p11 (subsetConv c0 p01) = subsetConv c1 p00 := by
      apply btree_ext; intro S₀
      rw [← hright, btreeGet_btreeMap2, btreeGet_btreeMap2]
      omega
    rw [hrem_eq]
    have hrem_le : treeLe (subsetConv c1 p00) p11 :=
      hright ▸ treeLe_add_right (subsetConv c0 p01) (subsetConv c1 p00)
    have hrem_lt : treeAllLt base32Mod (subsetConv c1 p00) := treeAllLt_mono hrem_le hp1.2
    have ih1 := ih c1 p00 (subsetConv c1 p00) h1' rfl hp0.1 hrem_lt
    rw [ih1]

theorem subsetConv_connSpanning {k : Nat} (G : SimpleGraphN (k + 1)) :
    subsetConv (btreeOfFn k (fun T₀ => connSpanningSubgraphCount G (snocBool T₀ true)))
      (buildPow2Tree k (initGraph G).adj) =
    scaleByNeighbors (lastNeighbors G) (buildPow2Tree k (initGraph G).adj) := by
  let P₀ := buildPow2Tree k (initGraph G).adj
  let P₁ := scaleByNeighbors (lastNeighbors G) P₀
  apply btree_ext; intro U₀
  rw [btreeGet_subsetConv]
  have hp1 : btreeGet P₁ U₀ = spanningSubgraphCount G (snocBool U₀ true) := by
    have := buildPow2Tree_spec (k + 1) G (snocBool U₀ true)
    simpa [buildPow2Tree, btreeGet, P₁, P₀, lastNeighbors, initGraph] using this
  rw [hp1, spanning_snoc_true_decomp G U₀]
  refine listSum_congr ?_; intro T₀ _
  split
  · rw [btreeGet_btreeOfFn, buildPow2Tree_spec k (initGraph G) (diffMask U₀ T₀)]
  · rfl

theorem treeLe_allConnTree :
    ∀ {r : Nat} (G : SimpleGraphN r),
      treeLe (allConnTree (buildPow2Tree r G.adj)) (buildPow2Tree r G.adj)
  | 0, _ => by show 0 ≤ 1; omega
  | k + 1, G => by
    have h1 := leftmostLeaf_buildPow2Tree k (initGraph G).adj
    have hconv := subsetConv_connSpanning G
    have hsolve := solveConn_eq_of_subsetConv h1 hconv
    change treeLe (allConnTree (buildPow2Tree k (initGraph G).adj))
        (buildPow2Tree k (initGraph G).adj) ∧
      treeLe (solveConn (buildPow2Tree k (initGraph G).adj)
        (scaleByNeighbors (lastNeighbors G) (buildPow2Tree k (initGraph G).adj)))
        (scaleByNeighbors (lastNeighbors G) (buildPow2Tree k (initGraph G).adj))
    rw [hsolve]
    exact ⟨treeLe_allConnTree (initGraph G), treeLe_of_subsetConv h1 hconv⟩

theorem packedAllConn32_eq :
    ∀ {r : Nat} (_ : r ≤ 8) (G : SimpleGraphN r),
      packedAllConn32 r (packTree32 (buildPow2Tree r G.adj)) =
        packTree32 (allConnTree (buildPow2Tree r G.adj))
  | 0, _, _ => rfl
  | k + 1, hr, G => by
    have hk : k ≤ 8 := by omega
    let G₀ := initGraph G
    let P₀ := buildPow2Tree k G₀.adj
    let P₁ := scaleByNeighbors (lastNeighbors G) P₀
    have htree_lt := treeAllLt_buildPow2Tree_32 hr G.adj
    unfold buildPow2Tree at htree_lt
    simp only [treeAllLt_node] at htree_lt
    rcases htree_lt with ⟨hp0_lt, hp1_lt⟩
    have hlp0 := packTree32_lt P₀ hp0_lt
    change sNat (packTree32 P₀ + laneMod k * packTree32 P₁) (fun pv =>
      sNat (Nat.mod pv (laneMod k)) fun p0 =>
        sNat (Nat.div pv (laneMod k)) fun p1 =>
          Nat.add (packedAllConn32 k p0) (Nat.mul (laneMod k) (packedSolveConn32 k p0 p1))) =
      packTree32 (allConnTree P₀) + laneMod k * packTree32 (solveConn P₀ P₁)
    simp only [sNat_eq, nat_add_eq_op, nat_mul_eq_op, nat_mod_eq_op, nat_div_eq_op]
    rw [split32_lo hlp0, split32_hi hlp0, packedAllConn32_eq hk G₀]
    have hconv := subsetConv_connSpanning G
    have h1 := leftmostLeaf_buildPow2Tree k G₀.adj
    have hsolve := solveConn_eq_of_subsetConv h1 hconv
    rw [hsolve, packedSolveConn32_eq k _ P₀ P₁ h1 hconv hp0_lt hp1_lt]

/-! #### 40-Bit Vector Packing / Unpacking (`packVec40`, `unpackVec40`) -/

def packVec40 : List Nat → Nat
  | [] => 0
  | x :: xs => x + vecMod40 * packVec40 xs

def unpackVec40 : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v => sNat v fun vv => Nat.mod vv vecMod40 :: unpackVec40 k (Nat.div vv vecMod40)

@[simp] theorem sumByOrder_leaf (x : Nat) : sumByOrder (.leaf x) = [x] := rfl
@[simp] theorem sumByOrder_node {k : Nat} (l r : BTree Nat k) :
    sumByOrder (.node l r) = addNatVecs (sumByOrder l) (0 :: sumByOrder r) := rfl

theorem packVec40_addNatVecs :
    ∀ (xs ys : List Nat),
      packVec40 (addNatVecs xs ys) = packVec40 xs + packVec40 ys
  | [], ys => by simp [addNatVecs, packVec40]
  | x :: xs, [] => by simp [addNatVecs, packVec40]
  | x :: xs, y :: ys => by
    simp only [addNatVecs, packVec40, packVec40_addNatVecs xs ys, Nat.mul_add]
    omega

theorem packedSumByOrder32_eq :
    ∀ (r : Nat) (T : BTree Nat r),
      treeAllLt base32Mod T →
      packedSumByOrder32 r (packTree32 T) = packVec40 (sumByOrder T) := by
  intro r
  induction r with
  | zero =>
    intro T _
    cases T with | leaf x =>
    simp [packedSumByOrder32, packVec40]
  | succ k ih =>
    intro T h
    cases T with | node l r =>
    unfold packedSumByOrder32
    simp only [sNat_eq, packTree32_node, sumByOrder_node, nat_add_eq_op, nat_mul_eq_op, nat_mod_eq_op, nat_div_eq_op]
    have hll := packTree32_lt l h.1
    rw [split32_lo hll, split32_hi hll,
        ih l h.1, ih r h.2,
        packVec40_addNatVecs]
    simp [packVec40]

def listAllLt (L : List Nat) (B : Nat) : Prop := ∀ x ∈ L, x < B

theorem listAllLt_addNatVecs :
    ∀ {xs ys : List Nat} {B₁ B₂ : Nat},
      listAllLt xs B₁ → listAllLt ys B₂ → listAllLt (addNatVecs xs ys) (B₁ + B₂)
  | [], _ => fun _ hy z hz => by simp only [addNatVecs] at hz; have := hy z hz; omega
  | _ :: _, [] => fun hx _ z hz => by simp only [addNatVecs] at hz; have := hx z hz; omega
  | x :: xs, y :: ys => fun hx hy z hz => by
    simp only [addNatVecs] at hz
    rcases List.mem_cons.mp hz with rfl | hrest
    · have h1 := hx x (List.mem_cons_self ..)
      have h2 := hy y (List.mem_cons_self ..)
      omega
    · exact listAllLt_addNatVecs
        (fun a ha => hx a (List.mem_cons_of_mem _ ha))
        (fun b hb => hy b (List.mem_cons_of_mem _ hb))
        z hrest

theorem listAllLt_sumByOrder :
    ∀ (r : Nat) (T : BTree Nat r) (B : Nat), (0 < B) →
      treeAllLt B T → listAllLt (sumByOrder T) (B * 2 ^ r) := by
  intro r
  induction r with
  | zero =>
    intro T B _ hx z hz
    cases T with | leaf x =>
    change z ∈ [x] at hz
    rcases List.mem_singleton.mp hz with rfl
    simp only [treeAllLt_leaf] at hx
    omega
  | succ k ih =>
    intro T B hB h z hz
    cases T with | node l r =>
    change z ∈ addNatVecs (sumByOrder l) (0 :: sumByOrder r) at hz
    have ihl := ih l B hB h.1
    have ihr := ih r B hB h.2
    have hcons : listAllLt (0 :: sumByOrder r) (B * 2 ^ k) := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | har
      · exact Nat.mul_pos hB (pow2_pos k)
      · exact ihr a har
    have hsum : z < B * 2 ^ k + B * 2 ^ k := listAllLt_addNatVecs ihl hcons z hz
    have hpow : B * 2 ^ (k + 1) = B * 2 ^ k * 2 := by rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hpow]
    omega

theorem listAllLt_sumByOrder_40 {r : Nat} (hr : r ≤ 8) {T : BTree Nat r}
    (ht : treeAllLt (2 ^ triBound r) T) : listAllLt (sumByOrder T) vecMod40 := by
  have h1 := listAllLt_sumByOrder r T (2 ^ triBound r) (pow2_pos (triBound r)) ht
  rw [← Nat.pow_add] at h1
  have h37 := (triBound_le_29 hr).2
  have hle : 2 ^ (triBound r + r) ≤ vecMod40 := by
    rw [vecMod40_eq]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  intro x hx
  exact Nat.lt_of_lt_of_le (h1 x hx) hle

theorem packVec40_div_tail :
    ∀ (L : List Nat), listAllLt L vecMod40 → (packVec40 L) / vecMod40 = packVec40 L.tail
  | [], _ => rfl
  | x :: xs, hlt => by
    have hx : x < vecMod40 := hlt x (List.mem_cons_self ..)
    conv => lhs; unfold packVec40
    rw [Nat.add_comm x _, Nat.mul_add_div vecMod40_pos, Nat.div_eq_of_lt hx, Nat.add_zero]
    rfl

theorem unpackVec40_packVec40 :
    ∀ (xs : List Nat), listAllLt xs vecMod40 → unpackVec40 xs.length (packVec40 xs) = xs
  | [], _ => rfl
  | x :: xs, hlt => by
    have hx : x < vecMod40 := hlt x (List.mem_cons_self ..)
    simp only [List.length, unpackVec40, sNat_eq, packVec40, nat_mod_eq_op, nat_div_eq_op]
    have hlo : (x + vecMod40 * packVec40 xs) % vecMod40 = x := by
      rw [Nat.add_comm x _, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
    have hhi : (x + vecMod40 * packVec40 xs) / vecMod40 = packVec40 xs := by
      rw [Nat.add_comm x _, Nat.mul_add_div vecMod40_pos, Nat.div_eq_of_lt hx, Nat.add_zero]
    rw [hlo, hhi]
    congr 1
    exact unpackVec40_packVec40 xs (fun y hy => hlt y (List.mem_cons_of_mem _ hy))

theorem listAllLt_tail {L : List Nat} {B : Nat} (h : listAllLt L B) : listAllLt L.tail B := by
  cases L with
  | nil => intro _ hx; cases hx
  | cons _ _ => intro y hy; exact h y (List.mem_cons_of_mem _ hy)

theorem fastConnEdgeKey32_eq {n : Nat} (hn : n ≤ 8) (mask : Nat) :
    fastConnEdgeKey32 n mask = packVec40 (fastConnEdgeSubgraphVec (graphOfAdjMask n mask)) := by
  let G := graphOfAdjMask n mask
  let P := buildPow2Tree n G.adj
  let C := allConnTree P
  have hC_tri : treeAllLt (2 ^ triBound n) C :=
    treeAllLt_mono (treeLe_allConnTree G) (treeAllLt_buildPow2Tree n G.adj)
  have h29 := (triBound_le_29 hn).1
  have hle32 : 2 ^ triBound n ≤ base32Mod := by
    rw [base32Mod_eq]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hC_32 : treeAllLt base32Mod C := treeAllLt_of_le hle32 hC_tri
  unfold fastConnEdgeKey32 fastConnEdgeSubgraphVec
  simp only [sNat_eq, nat_div_eq_op]
  rw [packedBuildPow2_32_eq n mask n hn]
  change (packedSumByOrder32 n (packedAllConn32 n (packTree32 P))) / vecMod40 = packVec40 (sumByOrder C).tail
  rw [packedAllConn32_eq hn G, packedSumByOrder32_eq n C hC_32,
      packVec40_div_tail (sumByOrder C) (listAllLt_sumByOrder_40 hn hC_tri)]

theorem fastAllEdgeKey32_eq {n : Nat} (hn : n ≤ 8) (mask : Nat) :
    fastAllEdgeKey32 n mask = packVec40 (fastAllEdgeSubgraphVec (graphOfAdjMask n mask)) := by
  let G := graphOfAdjMask n mask
  let P := buildPow2Tree n G.adj
  have hP_tri : treeAllLt (2 ^ triBound n) P := treeAllLt_buildPow2Tree n G.adj
  have hP_32 : treeAllLt base32Mod P := treeAllLt_buildPow2Tree_32 hn G.adj
  unfold fastAllEdgeKey32 fastAllEdgeSubgraphVec
  simp only [sNat_eq, nat_div_eq_op]
  rw [packedBuildPow2_32_eq n mask n hn]
  change (packedSumByOrder32 n (packTree32 P)) / vecMod40 = packVec40 (sumByOrder P).tail
  rw [packedSumByOrder32_eq n P hP_32,
      packVec40_div_tail (sumByOrder P) (listAllLt_sumByOrder_40 hn hP_tri)]

theorem connEdgeSubgraphVec_mask_eq {n : Nat} (hn : n ≤ 8) (mask : Nat) :
    connEdgeSubgraphVec (graphOfAdjMask n mask) = unpackVec40 n (fastConnEdgeKey32 n mask) := by
  let G := graphOfAdjMask n mask
  rw [connEdgeSubgraphVec_eq_fast, fastConnEdgeKey32_eq hn mask]
  let C := allConnTree (buildPow2Tree n G.adj)
  have hC_tri : treeAllLt (2 ^ triBound n) C :=
    treeAllLt_mono (treeLe_allConnTree G) (treeAllLt_buildPow2Tree n G.adj)
  have hlt := listAllLt_tail (listAllLt_sumByOrder_40 hn hC_tri)
  have hlen : (fastConnEdgeSubgraphVec G).length = n := by
    simp [fastConnEdgeSubgraphVec, length_sumByOrder]
  have hunpack := unpackVec40_packVec40 (fastConnEdgeSubgraphVec G) hlt
  rw [hlen] at hunpack
  exact hunpack.symm

theorem allEdgeSubgraphVec_mask_eq {n : Nat} (hn : n ≤ 8) (mask : Nat) :
    allEdgeSubgraphVec (graphOfAdjMask n mask) = unpackVec40 n (fastAllEdgeKey32 n mask) := by
  let G := graphOfAdjMask n mask
  rw [allEdgeSubgraphVec_eq_fast, fastAllEdgeKey32_eq hn mask]
  let P := buildPow2Tree n G.adj
  have hP_tri : treeAllLt (2 ^ triBound n) P := treeAllLt_buildPow2Tree n G.adj
  have hlt := listAllLt_tail (listAllLt_sumByOrder_40 hn hP_tri)
  have hlen : (fastAllEdgeSubgraphVec G).length = n := by
    simp [fastAllEdgeSubgraphVec, length_sumByOrder]
  have hunpack := unpackVec40_packVec40 (fastAllEdgeSubgraphVec G) hlt
  rw [hlen] at hunpack
  exact hunpack.symm

/-! ### Part 4: Concrete `List (List Int)` Determinant (`detRows`) for Fast `polyEval (charPoly G) x` -/

theorem polyEval_normPoly (p : List Int) (x : Int) :
    polyEval (normPoly p) x = polyEval p x := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    unfold normPoly
    cases hcs : normPoly cs with
    | nil =>
      rw [hcs] at ih
      simp only [polyEval] at ih
      by_cases hc : (c == 0) = true
      · have hc0 : c = 0 := of_decide_eq_true (by simpa using hc)
        simp [hc, hc0, polyEval, ← ih]
      · have hcf := Bool.eq_false_iff.mpr hc
        simp [hcf, polyEval, ← ih]
    | cons b bs =>
      have ih' : polyEval (b :: bs) x = polyEval cs x := by rw [← hcs]; exact ih
      show c + x * polyEval (b :: bs) x = c + x * polyEval cs x
      rw [ih']

theorem polyEval_rawAdd (p q : List Int) (x : Int) :
    polyEval (rawAdd p q) x = polyEval p x + polyEval q x := by
  induction p generalizing q with
  | nil => simp [rawAdd, polyEval]
  | cons a as ih =>
    cases q with
    | nil => simp [rawAdd, polyEval]
    | cons b bs =>
      simp only [rawAdd, polyEval, ih, Int.mul_add]
      omega

theorem polyEval_polyAdd (p q : Poly) (x : Int) :
    polyEval (polyAdd p q) x = polyEval p x + polyEval q x := by
  rw [polyAdd, polyEval_normPoly, polyEval_rawAdd]

def intListSum : List Int → Int
  | [] => 0
  | a :: as => a + intListSum as

theorem polyEval_polySum (ps : List Poly) (x : Int) :
    polyEval (polySum ps) x = intListSum (ps.map fun p => polyEval p x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [polySum, List.map, intListSum, polyEval_polyAdd, ih]

theorem polyEval_rawScale (c : Int) (p : List Int) (x : Int) :
    polyEval (rawScale c p) x = c * polyEval p x := by
  induction p with
  | nil => simp [rawScale, polyEval]
  | cons a as ih =>
    simp only [rawScale, polyEval, ih, Int.mul_add]
    have hmul : x * (c * polyEval as x) = c * (x * polyEval as x) := by
      rw [← Int.mul_assoc, Int.mul_comm x c, Int.mul_assoc]
    rw [hmul]

theorem polyEval_rawMul (p q : List Int) (x : Int) :
    polyEval (rawMul p q) x = polyEval p x * polyEval q x := by
  induction p with
  | nil => simp [rawMul, polyEval]
  | cons a as ih =>
    unfold rawMul
    rw [polyEval_rawAdd, polyEval_rawScale]
    simp only [polyEval, Int.zero_add, ih, Int.add_mul, Int.mul_assoc]

theorem polyEval_polyMul (p q : Poly) (x : Int) :
    polyEval (polyMul p q) x = polyEval p x * polyEval q x := by
  rw [polyMul, polyEval_normPoly, polyEval_rawMul]

theorem polyEval_polyConst (c x : Int) : polyEval (polyConst c) x = c := by
  unfold polyConst
  rw [polyEval_normPoly]
  simp [polyEval]

theorem polyEval_signPoly (j : Nat) (x : Int) :
    polyEval (signPoly j) x = (if Nat.beq (Nat.mod j 2) 0 then 1 else -1) := by
  unfold signPoly
  simp only [nat_beq_eq_beq, nat_mod_eq_op]
  cases (j % 2 == 0) <;> simp [polyEval_polyConst]

theorem map_map_fn {α : Type u} {β : Type v} {γ : Type w} (L : List α) (f : α → β) (g : β → γ) :
    (L.map f).map g = L.map (fun x => g (f x)) := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp only [List.map, ih]

def dropAt {α : Type u} : Nat → List α → List α
  | _, [] => []
  | 0, _ :: xs => xs
  | j + 1, x :: xs => x :: dropAt j xs

theorem dropAt_allFin :
    ∀ (m : Nat) (j : Fin (m + 1)) {α : Type u} (g : Fin (m + 1) → α),
      dropAt j.val ((allFin (m + 1)).map g) =
        (allFin m).map (fun i => g (deleteIdx j i))
  | 0, j, _, g => by
    have hj0 : j.val = 0 := by omega
    simp [allFin, hj0, dropAt]
  | m + 1, j, _, g => by
    cases j using Fin.cases with
    | zero =>
      conv => lhs; unfold allFin; rw [List.map_cons, map_map_fn]
      simp only [Fin.val_zero, dropAt]
      refine List.map_congr_left fun i _ => ?_
      have hdel : deleteIdx (0 : Fin (m + 2)) i = i.succ := by
        apply Fin.ext; simp [deleteIdx]
      rw [hdel]
    | succ j' =>
      have hjv : j'.succ.val = j'.val + 1 := rfl
      rw [hjv]
      conv => lhs; unfold allFin; rw [List.map_cons, map_map_fn]
      unfold dropAt
      have ih := dropAt_allFin m j' (fun k => g k.succ)
      rw [ih]
      conv => rhs; unfold allFin; rw [List.map_cons, map_map_fn]
      congr 1
      · have hdel0 : deleteIdx j'.succ (0 : Fin (m + 1)) = 0 := by
          apply Fin.ext; simp [deleteIdx]
        rw [hdel0]
      · refine List.map_congr_left fun i _ => ?_
        have hdelS : deleteIdx j'.succ i.succ = (deleteIdx j' i).succ := by
          apply Fin.ext
          unfold deleteIdx
          have hcond : (i.succ.val < j'.succ.val) ↔ (i.val < j'.val) := by simp
          by_cases hi : i.val < j'.val
          · have hi' : i.succ.val < j'.succ.val := hcond.mpr hi
            simp [hi, hi']
          · have hi' : ¬ (i.succ.val < j'.succ.val) := fun h => hi (hcond.mp h)
            simp [hi, hi']
        rw [hdelS]

def foldIdxInt (step : Nat → Int → Int) : Nat → List Int → Int
  | _, [] => 0
  | j, c :: cs => step j c + foldIdxInt step (Nat.add j 1) cs

theorem foldIdxInt_allFin :
    ∀ (k : Nat) (off : Nat) (step : Nat → Int → Int) (f : Fin k → Int),
      foldIdxInt step off ((allFin k).map f) =
        intListSum ((allFin k).map (fun j => step (off + j.val) (f j)))
  | 0, _, _, _ => rfl
  | k + 1, off, step, f => by
    conv => lhs; unfold allFin; rw [List.map_cons, map_map_fn]
    conv => rhs; unfold allFin; rw [List.map_cons, map_map_fn]
    simp only [foldIdxInt, intListSum]
    have h0 : off + (0 : Fin (k + 1)).val = off := Nat.add_zero off
    rw [h0]
    congr 1
    rw [foldIdxInt_allFin k (Nat.add off 1) step (fun i => f i.succ)]
    refine congrArg intListSum (List.map_congr_left fun i _ => ?_)
    have heq : Nat.add off 1 + i.val = off + i.succ.val := by simp; omega
    rw [heq]

def detRows : Nat → List (List Int) → Int
  | 0, _ => 1
  | _ + 1, [] => 0
  | m + 1, r0 :: rs =>
    foldIdxInt (fun j c =>
      if c == 0 then 0
      else (if Nat.beq (Nat.mod j 2) 0 then (1 : Int) else -1) * c * detRows m (rs.map (dropAt j))) 0 r0

theorem polyEval_detPoly_eq_detRows :
    ∀ (n : Nat) (M : Fin n → Fin n → Poly) (x : Int),
      polyEval (detPoly M) x =
        detRows n ((allFin n).map fun i => (allFin n).map fun j => polyEval (M i j) x)
  | 0, _, x => polyEval_polyConst 1 x
  | m + 1, M, x => by
    unfold detPoly
    rw [polyEval_polySum, map_map_fn]
    let rowFn : Fin (m + 1) → List Int := fun i => (allFin (m + 1)).map fun j => polyEval (M i j) x
    have hrows : ((allFin (m + 1)).map rowFn) = rowFn 0 :: (allFin m).map (fun i => rowFn i.succ) := by
      conv => lhs; unfold allFin; rw [List.map_cons, map_map_fn]
    change _ = detRows (m + 1) ((allFin (m + 1)).map rowFn)
    rw [hrows]
    unfold detRows
    rw [foldIdxInt_allFin (m + 1) 0 _ (fun j => polyEval (M 0 j) x)]
    refine congrArg intListSum (List.map_congr_left fun j _ => ?_)
    rw [Nat.zero_add, polyEval_polyMul, polyEval_polyMul, polyEval_signPoly]
    by_cases hz : (polyEval (M 0 j) x == 0) = true
    · have hz0 : polyEval (M 0 j) x = 0 := of_decide_eq_true (by simpa using hz)
      simp [hz, hz0]
    · have hzf := Bool.eq_false_iff.mpr hz
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [polyEval_detPoly_eq_detRows m (submatrix 0 j M) x]
      congr 1
      rw [map_map_fn]
      refine List.map_congr_left fun i _ => ?_
      dsimp only [rowFn]
      rw [dropAt_allFin m j (fun col => polyEval (M i.succ col) x)]
      refine List.map_congr_left fun col _ => ?_
      have hdel0 : deleteIdx (0 : Fin (m + 1)) i = i.succ := by
        apply Fin.ext; simp [deleteIdx]
      unfold submatrix
      rw [hdel0]

def fastEvalCharPoly {n : Nat} (G : SimpleGraphN n) (x : Int) : Int :=
  detRows n ((allFin n).map fun i => (allFin n).map fun j =>
    if i == j then x else if G.adj i j then -1 else 0)

theorem polyEval_charPoly_eq_fast {n : Nat} (G : SimpleGraphN n) (x : Int) :
    polyEval (charPoly G) x = fastEvalCharPoly G x := by
  unfold charPoly fastEvalCharPoly
  rw [polyEval_detPoly_eq_detRows]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  refine List.map_congr_left fun j _ => ?_
  unfold charMatrix
  by_cases hij : i = j
  · subst hij; simp [polyX, polyEval]
  · have hb : (i == j) = false :=
      Bool.eq_false_iff.mpr fun e => hij (of_decide_eq_true (by simpa using e))
    simp only [hij, hb, Bool.false_eq_true, ↓reduceIte]
    cases G.adj i j
    · rfl
    · exact polyEval_polyConst (-1) x

end Conjecture00000003970
