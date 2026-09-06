import LeanCo.QuantumLatin.Defs
import Mathlib.Tactic

/-!
# Finite classical Latin-square certificates

This file records the finite mutually orthogonal Latin squares needed by the
singular-product part of Zhang--Cao.  The order `10`, `14`, `15`, and `18`
tables are transcriptions of SageMath's public combinatorial-design database
(`src/sage/combinat/designs/database.py`, functions `MOLS_10_2`,
`MOLS_14_4`, `MOLS_15_4`, and `MOLS_18_3`).  Sage's string encoding lists one
row from each square in turn; `decodeInterleaved` implements exactly that
convention.  The order-nine certificate is the elementary construction over
`GF(9) = GF(3)[X]/(X^2+1)`.  The order-twenty-one certificate is the standard
PBD construction on the twenty-one lines of `PG(2,4)`, using three mutually
orthogonal idempotent Latin squares of order five inside every line.

All certificate checks below are closed decidable propositions.  In
particular, no property of these tables is trusted merely because it came
from the external database.
-/

namespace LeanCo.QuantumLatin

attribute [local instance] Fintype.decidableForallFintype

/-- A classical square of order `n`, with rows, columns, and symbols all
indexed by `Fin n`. -/
abbrev ClassicalSquare (n : ℕ) := Fin n → Fin n → Fin n

/-- The Latin property.  Since domain and codomain are the same finite type,
injectivity says exactly that every row and every column is a permutation of
all symbols. -/
def IsLatin {n : ℕ} (L : ClassicalSquare n) : Prop :=
  (∀ i a b, L i a = L i b → a = b) ∧
    ∀ j a b, L a j = L b j → a = b

/-- Two Latin squares are orthogonal when the ordered symbol pair determines
the cell.  Equal finite cardinalities make this equivalent to every ordered
pair occurring exactly once. -/
def Orthogonal {n : ℕ} (L M : ClassicalSquare n) : Prop :=
  ∀ i j i' j',
    (L i j, M i j) = (L i' j', M i' j') → i = i' ∧ j = j'

/-- Pair the two symbols in a cell.  On the finite square domain,
surjectivity of this map is equivalent to the orthogonality check. -/
def classicalPairMap {n : ℕ} (L M : ClassicalSquare n) :
    Fin n × Fin n → Fin n × Fin n :=
  fun x ↦ (L x.1 x.2, M x.1 x.2)

/-- A checked right-inverse table for the paired symbols certifies
orthogonality without expanding a fourfold collision search. -/
theorem orthogonal_of_pairMap_rightInverse {n : ℕ}
    {L M : ClassicalSquare n} (inv : Fin n × Fin n → Fin n × Fin n)
    (h : Function.RightInverse inv (classicalPairMap L M)) :
    Orthogonal L M := by
  have hinj : Function.Injective (classicalPairMap L M) :=
    Finite.injective_iff_surjective.mpr h.surjective
  intro i j i' j' hij
  have hmap : classicalPairMap L M (i, j) =
      classicalPairMap L M (i', j') := by
    exact hij
  have hp : (i, j) = (i', j') := hinj hmap
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Decode a flattened inverse-permutation table. -/
def inversePairFromData (n : ℕ) (hn : 0 < n) (data : Array ℕ)
    (y : Fin n × Fin n) : Fin n × Fin n :=
  let k := data.getD (n * y.1.1 + y.2.1) 0
  (⟨(k / n) % n, Nat.mod_lt _ hn⟩,
    ⟨k % n, Nat.mod_lt _ hn⟩)

/-- Existence of two mutually orthogonal Latin squares. -/
def HasTwoMOLS (n : ℕ) : Prop :=
  ∃ L M : ClassicalSquare n,
    IsLatin L ∧ IsLatin M ∧ Orthogonal L M

/-- Existence of three mutually orthogonal Latin squares. -/
def HasThreeMOLS (n : ℕ) : Prop :=
  ∃ L M N : ClassicalSquare n,
    IsLatin L ∧ IsLatin M ∧ IsLatin N ∧
      Orthogonal L M ∧ Orthogonal L N ∧ Orthogonal M N

/-! ## Compact table decoder -/

/-- Decode `a`, `b`, ... as `0`, `1`, ... .  A missing character decodes as
zero so that the decoder is total; `EncodingWellFormed` separately verifies
that this fallback and the final reduction modulo `n` are never used by the
recorded data. -/
def letterAt (s : String) (j : ℕ) : ℕ :=
  match s.toList[j]? with
  | some c => c.toNat - 'a'.toNat
  | none => 0

/-- Read one row token from an array, again returning an invalid-looking
default on an out-of-range access rather than introducing a proof obligation
into the data representation. -/
def rowToken (rows : Array String) (i : ℕ) : String :=
  match rows[i]? with
  | some s => s
  | none => ""

/-- Decode rows interleaved in Sage's `_MOLS_from_string` order. -/
def decodeInterleaved (n k : ℕ) (hn : 0 < n) (rows : Array String)
    (which : Fin k) : ClassicalSquare n :=
  fun i j ↦
    ⟨letterAt (rowToken rows (i.1 * k + which.1)) j.1 % n,
      Nat.mod_lt _ hn⟩

/-- The syntactic side condition for a Sage table: exactly `n*k` row tokens,
each containing exactly `n` lower-case letters from the order-`n` alphabet. -/
def EncodingWellFormed (n k : ℕ) (rows : Array String) : Prop :=
  rows.size = n * k ∧
    ∀ i : Fin rows.size,
      (rows[i].toList).length = n ∧
        ∀ j : Fin (rows[i].toList).length,
          'a'.toNat ≤ (rows[i].toList)[j].toNat ∧
            (rows[i].toList)[j].toNat < 'a'.toNat + n

/-! ## Order nine: three field-linear squares over `GF(9)` -/

/-- Encode a pair of ternary coefficients as an element of `Fin 9`. -/
def gf9Encode (a b : ℕ) : Fin 9 :=
  ⟨(3 * (a % 3) + b % 3) % 9, Nat.mod_lt _ (by decide)⟩

/-- Decode the coefficient of `1` in `GF(3)[X]/(X²+1)`. -/
def gf9Re (x : Fin 9) : ℕ := x.1 / 3

/-- Decode the coefficient of `X` in `GF(3)[X]/(X²+1)`. -/
def gf9Im (x : Fin 9) : ℕ := x.1 % 3

/-- Addition in the chosen concrete model of `GF(9)`. -/
def gf9Add (x y : Fin 9) : Fin 9 :=
  gf9Encode (gf9Re x + gf9Re y) (gf9Im x + gf9Im y)

/-- Multiplication modulo `X²+1`, so `X² = -1 = 2` in `GF(3)`. -/
def gf9Mul (x y : Fin 9) : Fin 9 :=
  gf9Encode (gf9Re x * gf9Re y + 2 * gf9Im x * gf9Im y)
    (gf9Re x * gf9Im y + gf9Im x * gf9Re y)

/-- The field-linear Latin square `x + slope*y`. -/
def gf9Square (slope : Fin 9) : ClassicalSquare 9 :=
  fun x y ↦ gf9Add x (gf9Mul slope y)

/-- Slopes `1`, `X`, and `1+X`, respectively. -/
def mols9A : ClassicalSquare 9 := gf9Square ⟨3, by decide⟩
def mols9B : ClassicalSquare 9 := gf9Square ⟨1, by decide⟩
def mols9C : ClassicalSquare 9 := gf9Square ⟨4, by decide⟩

theorem mols9A_latin : IsLatin mols9A := by
  unfold IsLatin
  decide +kernel
theorem mols9B_latin : IsLatin mols9B := by
  unfold IsLatin
  decide +kernel
theorem mols9C_latin : IsLatin mols9C := by
  unfold IsLatin
  decide +kernel
theorem mols9AB_orthogonal : Orthogonal mols9A mols9B := by
  unfold Orthogonal
  decide +kernel
theorem mols9AC_orthogonal : Orthogonal mols9A mols9C := by
  unfold Orthogonal
  decide +kernel
theorem mols9BC_orthogonal : Orthogonal mols9B mols9C := by
  unfold Orthogonal
  decide +kernel

theorem hasThreeMOLS_nine : HasThreeMOLS 9 := by
  exact ⟨mols9A, mols9B, mols9C, mols9A_latin, mols9B_latin,
    mols9C_latin, mols9AB_orthogonal, mols9AC_orthogonal,
    mols9BC_orthogonal⟩

theorem hasThreeMOLS_9 : HasThreeMOLS 9 := hasThreeMOLS_nine

/-! ## Order ten: SageMath `MOLS_10_2` -/

def rows10 : Array String := #[
  "bijacegdfh", "bhgfajicde",
  "hcijadfegb", "icbhgajdef",
  "gbdijaefhc", "jidcbhaefg",
  "fhceijagbd", "ajiedcbfgh",
  "agbdfijhce", "cajifedghb",
  "jahcegibdf", "edajigfhbc",
  "ijabdfhceg", "gfeajihbcd",
  "cdefghbija", "defghbciaj",
  "defghbcaij", "fghbcdeaji",
  "efghbcdjai", "hbcdefgjia"
]

theorem rows10_wellFormed : EncodingWellFormed 10 2 rows10 := by
  unfold EncodingWellFormed
  decide +kernel

def mols10A : ClassicalSquare 10 :=
  decodeInterleaved 10 2 (by decide) rows10 ⟨0, by decide⟩

def mols10B : ClassicalSquare 10 :=
  decodeInterleaved 10 2 (by decide) rows10 ⟨1, by decide⟩

theorem mols10A_latin : IsLatin mols10A := by
  unfold IsLatin
  decide +kernel
theorem mols10B_latin : IsLatin mols10B := by
  unfold IsLatin
  decide +kernel
theorem mols10AB_orthogonal : Orthogonal mols10A mols10B := by
  unfold Orthogonal
  decide +kernel

theorem hasTwoMOLS_ten : HasTwoMOLS 10 := by
  exact ⟨mols10A, mols10B, mols10A_latin, mols10B_latin,
    mols10AB_orthogonal⟩

theorem hasTwoMOLS_10 : HasTwoMOLS 10 := hasTwoMOLS_ten

/-! ## Order fourteen: the first three squares of SageMath `MOLS_14_4` -/

def rows14 : Array String := #[
  "bjihgkecalnfmd", "bfmcenidgjhalk", "bcdefghijklmna",
  "fckjbhledimagn", "jcgndfalehkbim", "gnkjdmiclbhaef",
  "mgdlkcbafejnih", "ikdhaegnmfblcj", "lifhbjemkangcd",
  "cnhemldbigfkaj", "hjlebifkangcmd", "dalmgnbjehcfik",
  "edabfnmkcjhgli", "gbkmfcjeliahdn", "njcaeifhbdgkml",
  "nfeicgajldkbhm", "khclngdafmjibe", "mfbkcdlagnjihe",
  "iagfjdhnkmelcb", "elbdmahfignkjc", "aemnhkjdcifblg",
  "dlnkeafimhcjbg", "ceabkjnihdmgfl", "hdnikbagmcelfj",
  "gemalfihjnbdkc", "adficlkmjbenhg", "cgjflhnbiekdam",
  "jhfnimgdbkacel", "liegjdmhnkcfab", "fkibmagenldhjc",
  "hkbgajnmeclidf", "nmjfhkecbaldgi", "imhlneckdfajgb",
  "ablchikgnfdmje", "fankgbljdcimeh", "klegafdnhjmcbi",
  "licmdbjfhagenk", "mgialhcbkedjnf", "jhadicmlfgbekn",
  "kmjdneclgbihfa", "dnhjimbgclfeka", "ebgcjlkfamindh"
]

theorem rows14_wellFormed : EncodingWellFormed 14 3 rows14 := by
  unfold EncodingWellFormed
  decide +kernel

def mols14A : ClassicalSquare 14 :=
  decodeInterleaved 14 3 (by decide) rows14 ⟨0, by decide⟩
def mols14B : ClassicalSquare 14 :=
  decodeInterleaved 14 3 (by decide) rows14 ⟨1, by decide⟩
def mols14C : ClassicalSquare 14 :=
  decodeInterleaved 14 3 (by decide) rows14 ⟨2, by decide⟩

theorem mols14A_latin : IsLatin mols14A := by
  unfold IsLatin
  decide +kernel
theorem mols14B_latin : IsLatin mols14B := by
  unfold IsLatin
  decide +kernel
theorem mols14C_latin : IsLatin mols14C := by
  unfold IsLatin
  decide +kernel
theorem mols14AB_orthogonal : Orthogonal mols14A mols14B := by
  unfold Orthogonal
  decide +kernel
theorem mols14AC_orthogonal : Orthogonal mols14A mols14C := by
  unfold Orthogonal
  decide +kernel
theorem mols14BC_orthogonal : Orthogonal mols14B mols14C := by
  unfold Orthogonal
  decide +kernel

theorem hasThreeMOLS_fourteen : HasThreeMOLS 14 := by
  exact ⟨mols14A, mols14B, mols14C, mols14A_latin, mols14B_latin,
    mols14C_latin, mols14AB_orthogonal, mols14AC_orthogonal,
    mols14BC_orthogonal⟩

theorem hasThreeMOLS_14 : HasThreeMOLS 14 := hasThreeMOLS_fourteen

/-! ## Order fifteen: the first three squares of SageMath `MOLS_15_4` -/

def rows15 : Array String := #[
  "bcdefghijklmnoa", "bdgiknfcamehjlo", "bhealiofmdjgcnk",
  "abcdefghijklmno", "acehjlogdbnfikm", "lcifbmjagnekhdo",
  "oabcdefghijklmn", "nbdfikmahecogjl", "amdjgcnkbhoflie",
  "noabcdefghijklm", "mocegjlnbifdahk", "fbnekhdolciagmj",
  "mnoabcdefghijkl", "lnadfhkmocjgebi", "kgcoflieamdjbhn",
  "lmnoabcdefghijk", "jmobegilnadkhfc", "olhdagmjfbnekci",
  "klmnoabcdefghij", "dknacfhjmobelig", "jamiebhnkgcofld",
  "jklmnoabcdefghi", "helobdgiknacfmj", "ekbnjfciolhdagm",
  "ijklmnoabcdefgh", "kifmacehjlobdgn", "nflcokgdjamiebh",
  "hijklmnoabcdefg", "oljgnbdfikmaceh", "iogmdalhekbnjfc",
  "ghijklmnoabcdef", "iamkhocegjlnbdf", "djahnebmiflcokg",
  "fghijklmnoabcde", "gjbnliadfhkmoce", "hekbiofcnjgmdal",
  "efghijklmnoabcd", "fhkcomjbegilnad", "miflcjagdokhneb",
  "defghijklmnoabc", "egildankcfhjmob", "cnjgmdkbhealiof",
  "cdefghijklmnoab", "cfhjmeboldgikna", "gdokhnelcifbmja"
]

theorem rows15_wellFormed : EncodingWellFormed 15 3 rows15 := by
  unfold EncodingWellFormed
  decide +kernel

def mols15A : ClassicalSquare 15 :=
  decodeInterleaved 15 3 (by decide) rows15 ⟨0, by decide⟩
def mols15B : ClassicalSquare 15 :=
  decodeInterleaved 15 3 (by decide) rows15 ⟨1, by decide⟩
def mols15C : ClassicalSquare 15 :=
  decodeInterleaved 15 3 (by decide) rows15 ⟨2, by decide⟩

theorem mols15A_latin : IsLatin mols15A := by
  unfold IsLatin
  decide +kernel
theorem mols15B_latin : IsLatin mols15B := by
  unfold IsLatin
  decide +kernel
theorem mols15C_latin : IsLatin mols15C := by
  unfold IsLatin
  decide +kernel
theorem mols15AB_orthogonal : Orthogonal mols15A mols15B := by
  unfold Orthogonal
  decide +kernel
theorem mols15AC_orthogonal : Orthogonal mols15A mols15C := by
  unfold Orthogonal
  decide +kernel
theorem mols15BC_orthogonal : Orthogonal mols15B mols15C := by
  unfold Orthogonal
  decide +kernel

theorem hasThreeMOLS_fifteen : HasThreeMOLS 15 := by
  exact ⟨mols15A, mols15B, mols15C, mols15A_latin, mols15B_latin,
    mols15C_latin, mols15AB_orthogonal, mols15AC_orthogonal,
    mols15BC_orthogonal⟩

theorem hasThreeMOLS_15 : HasThreeMOLS 15 := hasThreeMOLS_fifteen

/-! ## Order eighteen: SageMath `MOLS_18_3` -/

def rows18 : Array String := #[
  "bgejhkmodcnarilpfq", "beqpodgcflkrjahnim", "bcdefghijklmnopqra",
  "echfbilnprdokajmqg", "gcfrqpehdnmlabkioj", "rbkamfgdehqjinopcl",
  "qfdigcjmohaeplkbnr", "ehdgarqfibonmkcljp", "mlbqhifgajdcrenopk",
  "prgejhdbnaikfqmlco", "jfiehkargqcponldmb", "hijbcdefgqraklmnop",
  "oqahfbiecpkjlgrnmd", "hbgjfilkacrdqpomen", "gderbkamfpclhqjino",
  "dprkigcjfeqlbmhaon", "kichbgjmlodaerqpnf", "fgamlbqhiopkjdcren",
  "geqaljhdbofrmcnikp", "mljdichbngpekfarqo", "efghijbcdnopqraklm",
  "chfrkmbieqpgandojl", "onmbejdicphqflgkar", "amfgderbkinopclhqj",
  "fdigalncjmrqhkoepb", "dponcfbejaqirgmhlk", "qhifgamlbrenopkjdc",
  "lnbqcogpakmhdrifej", "crhapeoqmkbgidnjfl", "leqjponacbkidfgmhr",
  "kmocrdphqblnieajgf", "ndaikqfprmlchjeobg", "kjmcrponhlbqeafgid",
  "rlnpdaeqigcmojfkbh", "aoekjlrgqhnmdibfpc", "dqriklponajbcmhfge",
  "jamoqekfrihdnpbglc", "rkpflbmahdionejcgq", "nacleqjpomhrbkidfg",
  "abknprflgdjieoqchm", "ialqgmcnkrejpofbdh", "onhkjmcrpgidlbqeaf",
  "hkcloqagmnebjfprdi", "ljkmrhndoiafbqpgce", "pondqriklfgeajbcmh",
  "nildmprkhjofcbgqae", "pmblnaioefjkgcrqhd", "jponacleqdfgmhrbki",
  "iojmenqalfbpgdchrk", "fqncmokjpegblhdari", "crponhkjmeafgidlbq",
  "mjpbnforklgcqhedia", "qgrodnplbjfhcmieka", "iklpondqrcmhfgeajb"
]

theorem rows18_wellFormed : EncodingWellFormed 18 3 rows18 := by
  unfold EncodingWellFormed
  decide +kernel

def mols18A : ClassicalSquare 18 :=
  decodeInterleaved 18 3 (by decide) rows18 ⟨0, by decide⟩
def mols18B : ClassicalSquare 18 :=
  decodeInterleaved 18 3 (by decide) rows18 ⟨1, by decide⟩
def mols18C : ClassicalSquare 18 :=
  decodeInterleaved 18 3 (by decide) rows18 ⟨2, by decide⟩

def inv18ABData : Array Nat := #[323,31,148,111,194,138,74,286,234,295,217,203,170,258,46,105,63,11,235,0,283,132,102,263,298,164,77,230,161,51,189,116,309,214,22,61,80,249,19,302,151,121,282,317,183,96,254,9,70,208,126,166,233,41,60,115,268,38,321,8,140,301,174,202,90,273,28,89,227,145,185,243,262,221,134,287,57,178,18,159,320,193,79,109,292,47,99,246,2,204,223,212,240,144,297,76,197,37,16,177,281,98,128,311,66,118,265,21,40,196,231,259,1,316,95,207,56,35,242,300,108,147,168,85,137,284,303,45,215,250,278,20,173,114,226,75,59,252,319,127,4,187,104,156,13,94,64,225,269,288,39,192,133,245,322,78,271,176,146,23,206,123,142,264,113,83,244,279,307,58,211,152,32,179,97,290,195,3,42,216,30,314,50,5,130,213,157,93,305,253,171,236,222,180,277,65,124,82,101,272,162,69,24,149,232,14,112,315,49,190,255,241,199,296,84,143,153,172,291,181,88,43,6,251,33,131,120,68,209,274,260,218,306,103,122,150,191,310,200,107,62,25,261,52,10,139,87,228,293,270,237,163,182,71,7,210,167,219,117,72,44,280,141,29,158,106,247,312,289,256,275,299,81,26,229,186,238,136,91,54,201,160,48,15,125,266,169,308,165,73,318,100,36,248,205,257,155,110,294,220,17,67,34,135,285,188,198,129,92,175,119,55,267,224,276,12,184,313,239,27,86,53,154,304]

def inv18ACData : Array Nat := #[217,323,170,46,74,194,148,111,258,295,286,203,11,31,234,138,63,105,298,0,161,116,263,61,214,283,230,102,77,189,22,235,51,309,164,132,126,19,183,302,249,80,233,317,41,208,9,151,282,254,70,166,96,121,321,38,115,174,60,90,243,145,301,8,202,140,268,273,89,185,28,227,193,57,47,2,320,109,262,178,287,159,134,246,79,292,99,204,221,18,21,76,240,197,297,128,281,212,98,265,66,37,177,311,118,223,144,16,207,95,1,231,108,147,300,40,196,56,259,35,316,168,137,242,85,284,250,114,104,59,215,4,319,226,173,45,20,303,127,187,156,252,278,75,78,133,288,245,192,23,176,269,146,322,123,94,225,206,13,271,39,64,264,152,58,279,3,42,195,97,244,113,307,83,211,216,32,290,142,179,65,171,82,130,277,213,5,236,30,222,180,124,93,50,253,157,305,314,149,190,315,255,49,232,24,84,112,143,101,162,296,69,272,14,199,241,274,209,218,103,131,251,43,6,306,181,172,260,68,88,291,33,120,153,122,228,139,25,163,261,62,293,87,270,237,10,150,107,310,52,191,200,44,247,210,312,106,280,72,141,7,29,158,219,182,117,167,71,256,289,169,266,275,160,26,299,91,54,201,238,229,308,125,136,186,81,15,48,17,285,34,73,220,318,110,188,135,165,294,67,36,155,205,100,248,257,92,304,267,198,154,175,129,27,55,86,53,276,239,12,224,119,313,184]

def inv18BCData : Array Nat := #[122,323,275,198,60,80,262,40,30,165,101,303,182,235,13,223,142,153,264,0,115,73,249,299,129,212,196,45,172,94,150,31,272,71,221,314,92,19,240,231,215,318,148,283,7,113,134,162,268,50,291,81,191,64,250,38,210,302,26,175,5,111,287,181,259,83,225,69,310,100,144,132,321,57,1,130,297,194,24,269,244,102,229,151,36,88,167,119,278,200,149,76,288,279,263,213,43,178,55,8,20,219,316,107,186,138,248,121,298,95,267,197,74,232,62,6,173,238,307,140,282,117,205,157,39,18,207,114,58,25,192,251,72,317,301,159,286,37,93,136,224,14,164,257,44,133,183,174,320,261,91,226,112,56,77,276,211,155,234,33,305,16,193,152,315,245,131,280,110,54,230,295,202,35,177,12,253,52,96,75,217,171,161,59,49,90,281,141,201,322,294,10,79,254,32,242,120,184,78,190,139,160,220,109,300,236,98,29,9,203,68,273,51,252,313,179,17,209,170,255,108,128,319,97,87,222,158,189,239,292,70,271,28,48,274,228,47,116,106,147,176,27,258,208,180,67,127,311,89,290,15,241,126,247,34,46,277,4,195,293,146,86,66,260,125,168,99,309,199,227,65,266,218,312,3,23,214,145,135,270,53,246,296,187,118,166,85,105,169,285,104,2,154,42,233,84,306,265,237,124,22,206,137,185,63,289,21,304,82,103,163,61,243,188,41,143,123,308,11,216,156,204,256,284]

def inv18AB : Fin 18 × Fin 18 → Fin 18 × Fin 18 :=
  inversePairFromData 18 (by decide) inv18ABData

def inv18AC : Fin 18 × Fin 18 → Fin 18 × Fin 18 :=
  inversePairFromData 18 (by decide) inv18ACData

def inv18BC : Fin 18 × Fin 18 → Fin 18 × Fin 18 :=
  inversePairFromData 18 (by decide) inv18BCData

set_option maxHeartbeats 0 in
theorem inv18AB_rightInverse :
    Function.RightInverse inv18AB (classicalPairMap mols18A mols18B) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem inv18AC_rightInverse :
    Function.RightInverse inv18AC (classicalPairMap mols18A mols18C) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem inv18BC_rightInverse :
    Function.RightInverse inv18BC (classicalPairMap mols18B mols18C) := by
  decide +kernel

theorem mols18A_latin : IsLatin mols18A := by
  unfold IsLatin
  decide +kernel
theorem mols18B_latin : IsLatin mols18B := by
  unfold IsLatin
  decide +kernel
theorem mols18C_latin : IsLatin mols18C := by
  unfold IsLatin
  decide +kernel
theorem mols18AB_orthogonal : Orthogonal mols18A mols18B := by
  exact orthogonal_of_pairMap_rightInverse inv18AB inv18AB_rightInverse
theorem mols18AC_orthogonal : Orthogonal mols18A mols18C := by
  exact orthogonal_of_pairMap_rightInverse inv18AC inv18AC_rightInverse
theorem mols18BC_orthogonal : Orthogonal mols18B mols18C := by
  exact orthogonal_of_pairMap_rightInverse inv18BC inv18BC_rightInverse

theorem hasThreeMOLS_eighteen : HasThreeMOLS 18 := by
  exact ⟨mols18A, mols18B, mols18C, mols18A_latin, mols18B_latin,
    mols18C_latin, mols18AB_orthogonal, mols18AC_orthogonal,
    mols18BC_orthogonal⟩

theorem hasThreeMOLS_18 : HasThreeMOLS 18 := hasThreeMOLS_eighteen

/-! ## Order twenty-one: the projective plane `PG(2,4)`

We present `PG(2,4)` as the affine plane over `GF(4)`, together with its five
points at infinity.  Affine points `(x,y)` have code `4*x+y`; the four finite
slopes have codes `16,...,19`, and the vertical point has code `20`.  Lines
are encoded in the analogous order: `y = m*x+b`, then the four vertical
lines, then the line at infinity.

Every two distinct points determine a five-point line.  On that line, with
local coordinates `i,j : Fin 5`, the operations

* `2*i + 4*j`,
* `3*i + 3*j`, and
* `4*i + 2*j`

(modulo five) are three mutually orthogonal idempotent Latin squares.  The
idempotence makes the linewise definitions agree on diagonal cells, giving
the PBD construction of three MOLS of order twenty-one.
-/

/-! ### A concrete four-element field -/

/-- Encode `a + bα` in `GF(4) = GF(2)[α]/(α²+α+1)` as `2*a+b`. -/
def gf4EncodeNat (a b : ℕ) : ℕ :=
  2 * (a % 2) + b % 2

/-- Coefficient of `1` in the concrete `GF(4)` encoding. -/
def gf4ReNat (x : ℕ) : ℕ := (x % 4) / 2

/-- Coefficient of `α` in the concrete `GF(4)` encoding. -/
def gf4ImNat (x : ℕ) : ℕ := x % 2

/-- Addition in the concrete `GF(4)` encoding. -/
def gf4AddNat (x y : ℕ) : ℕ :=
  gf4EncodeNat (gf4ReNat x + gf4ReNat y) (gf4ImNat x + gf4ImNat y)

/-- Multiplication with `α² = α+1` in characteristic two. -/
def gf4MulNat (x y : ℕ) : ℕ :=
  gf4EncodeNat
    (gf4ReNat x * gf4ReNat y + gf4ImNat x * gf4ImNat y)
    (gf4ReNat x * gf4ImNat y + gf4ImNat x * gf4ReNat y +
      gf4ImNat x * gf4ImNat y)

/-- Multiplicative inverse in the concrete encoding; zero is sent to zero so
the function remains total. -/
def gf4InvNat (x : ℕ) : ℕ :=
  match x % 4 with
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | _ => 0

/-- Reduce a natural-number point code to `Fin 21`. -/
def fin21 (x : ℕ) : Fin 21 :=
  ⟨x % 21, Nat.mod_lt _ (by decide)⟩

/-! ### Incidence and local coordinates in `PG(2,4)` -/

/-- The point in local position `pos` on the projective-plane line `line`.
Only inputs `line < 21` and `pos < 5` are used by the construction; reduction
to `Fin 21` keeps the definition total. -/
def pg21BlockPoint (line pos : ℕ) : Fin 21 :=
  if line < 16 then
    let m := line / 4
    let b := line % 4
    if pos < 4 then
      fin21 (4 * pos + gf4AddNat (gf4MulNat m pos) b)
    else
      fin21 (16 + m)
  else if line < 20 then
    let b := line - 16
    if pos < 4 then
      fin21 (4 * b + pos)
    else
      fin21 20
  else
    fin21 (16 + pos)

/-- The code of the unique projective-plane line through two distinct points.
Its value on equal points is immaterial to `pbdSquare21`, which treats the
diagonal separately. -/
def pg21Line (p q : Fin 21) : ℕ :=
  let u := p.1
  let v := q.1
  if u < 16 then
    let x₁ := u / 4
    let y₁ := u % 4
    if v < 16 then
      let x₂ := v / 4
      let y₂ := v % 4
      if x₁ = x₂ then
        16 + x₁
      else
        let m := gf4MulNat (gf4AddNat y₁ y₂)
          (gf4InvNat (gf4AddNat x₁ x₂))
        let b := gf4AddNat y₁ (gf4MulNat m x₁)
        4 * m + b
    else if v = 20 then
      16 + x₁
    else
      let m := v - 16
      let b := gf4AddNat y₁ (gf4MulNat m x₁)
      4 * m + b
  else if v < 16 then
    let x₂ := v / 4
    let y₂ := v % 4
    if u = 20 then
      16 + x₂
    else
      let m := u - 16
      let b := gf4AddNat y₂ (gf4MulNat m x₂)
      4 * m + b
  else
    20

/-- Local coordinate, from zero to four, of a point on an encoded line. -/
def pg21Position (line : ℕ) (p : Fin 21) : ℕ :=
  if line < 16 then
    if p.1 < 16 then p.1 / 4 else 4
  else if line < 20 then
    if p.1 < 16 then p.1 % 4 else 4
  else
    p.1 - 16

/-! ### The three PBD-composed squares and their closed checks -/

/-- Compose an idempotent order-five operation, specified by its two
coefficients, over every line of `PG(2,4)`. -/
def pbdSquare21 (left right : ℕ) : ClassicalSquare 21 :=
  fun p q ↦
    if p = q then
      p
    else
      let line := pg21Line p q
      let i := pg21Position line p
      let j := pg21Position line q
      pg21BlockPoint line ((left * i + right * j) % 5)

def mols21A : ClassicalSquare 21 := pbdSquare21 2 4
def mols21B : ClassicalSquare 21 := pbdSquare21 3 3
def mols21C : ClassicalSquare 21 := pbdSquare21 4 2

def mols21ABInverseDataKernel : Array ℕ := #[0, 423, 64, 62, 348, 393, 412, 371, 256, 301, 320, 279, 184, 250, 206, 228, 92, 156, 115, 137, 23,
  45, 22, 20, 422, 392, 349, 372, 411, 321, 278, 259, 298, 229, 205, 249, 185, 114, 134, 95, 157, 63,
  421, 83, 44, 21, 414, 369, 350, 391, 280, 319, 300, 257, 248, 186, 226, 208, 136, 116, 155, 93, 3,
  41, 2, 420, 66, 370, 413, 390, 351, 299, 258, 277, 322, 207, 227, 187, 247, 158, 94, 135, 113, 43,
  180, 245, 204, 223, 88, 427, 152, 146, 16, 61, 80, 39, 344, 367, 389, 408, 252, 276, 295, 317, 111,
  225, 202, 243, 182, 133, 110, 104, 426, 82, 37, 18, 59, 368, 345, 407, 388, 274, 254, 315, 297, 151,
  244, 183, 224, 201, 425, 167, 132, 109, 38, 81, 58, 19, 387, 410, 346, 365, 296, 316, 255, 273, 91,
  203, 222, 181, 246, 125, 90, 424, 154, 60, 17, 40, 79, 409, 386, 366, 347, 318, 294, 275, 253, 131,
  340, 363, 385, 404, 268, 313, 332, 291, 176, 431, 240, 230, 84, 149, 108, 127, 12, 36, 55, 77, 199,
  364, 341, 403, 384, 334, 289, 270, 311, 221, 198, 188, 430, 129, 106, 147, 86, 34, 14, 75, 57, 239,
  383, 406, 342, 361, 290, 333, 310, 271, 429, 251, 220, 197, 148, 87, 128, 105, 56, 76, 15, 33, 179,
  405, 382, 362, 343, 312, 269, 292, 331, 209, 178, 428, 242, 107, 126, 85, 150, 78, 54, 35, 13, 219,
  100, 166, 122, 144, 8, 53, 72, 31, 336, 381, 400, 359, 264, 435, 328, 314, 172, 236, 195, 217, 287,
  145, 121, 165, 101, 73, 30, 11, 50, 380, 337, 360, 399, 309, 286, 272, 434, 194, 214, 175, 237, 327,
  164, 102, 142, 124, 32, 71, 52, 9, 402, 357, 338, 379, 433, 335, 308, 285, 216, 196, 235, 173, 267,
  123, 143, 103, 163, 51, 10, 29, 74, 358, 401, 378, 339, 293, 266, 432, 330, 238, 174, 215, 193, 307,
  260, 282, 304, 326, 168, 190, 212, 234, 96, 118, 140, 162, 4, 26, 48, 70, 352, 439, 416, 398, 375,
  303, 323, 263, 283, 213, 233, 169, 189, 141, 161, 97, 117, 47, 67, 7, 27, 397, 374, 356, 438, 415,
  325, 305, 281, 261, 232, 210, 192, 170, 160, 138, 120, 98, 69, 49, 25, 5, 437, 419, 396, 373, 355,
  284, 262, 324, 302, 191, 171, 231, 211, 119, 99, 159, 139, 28, 6, 68, 46, 377, 354, 436, 418, 395,
  65, 42, 24, 1, 153, 130, 112, 89, 241, 218, 200, 177, 329, 306, 288, 265, 417, 394, 376, 353, 440
]

def mols21ABInverseKernel : Fin 21 × Fin 21 → Fin 21 × Fin 21 :=
  inversePairFromData 21 (by decide) mols21ABInverseDataKernel

set_option maxHeartbeats 0 in
theorem mols21AB_rightInverse_kernel :
    Function.RightInverse mols21ABInverseKernel
      (classicalPairMap mols21A mols21B) := by
  decide +kernel

theorem mols21AB_orthogonal_kernel : Orthogonal mols21A mols21B :=
  orthogonal_of_pairMap_rightInverse mols21ABInverseKernel
    mols21AB_rightInverse_kernel

def mols21ACInverseDataKernel : Array ℕ := #[0, 62, 423, 23, 184, 228, 250, 206, 348, 371, 393, 412, 92, 137, 156, 115, 256, 301, 320, 279, 64,
  422, 22, 63, 20, 249, 205, 185, 229, 372, 349, 411, 392, 157, 114, 95, 134, 278, 321, 298, 259, 45,
  83, 3, 44, 421, 208, 248, 226, 186, 391, 414, 350, 369, 116, 155, 136, 93, 300, 257, 280, 319, 21,
  43, 420, 41, 66, 227, 187, 207, 247, 413, 390, 370, 351, 135, 94, 113, 158, 322, 277, 258, 299, 2,
  344, 389, 408, 367, 88, 146, 427, 111, 252, 317, 276, 295, 16, 80, 39, 61, 180, 223, 245, 204, 152,
  388, 345, 368, 407, 426, 110, 151, 104, 297, 274, 315, 254, 59, 37, 82, 18, 202, 243, 225, 182, 133,
  410, 365, 346, 387, 167, 91, 132, 425, 316, 255, 296, 273, 81, 19, 58, 38, 224, 183, 201, 244, 109,
  366, 409, 386, 347, 131, 424, 125, 154, 275, 294, 253, 318, 40, 60, 17, 79, 246, 203, 181, 222, 90,
  268, 332, 291, 313, 12, 77, 36, 55, 176, 230, 431, 199, 340, 385, 404, 363, 84, 127, 149, 108, 240,
  311, 289, 334, 270, 57, 34, 75, 14, 430, 198, 239, 188, 384, 341, 364, 403, 106, 147, 129, 86, 221,
  333, 271, 310, 290, 76, 15, 56, 33, 251, 179, 220, 429, 406, 361, 342, 383, 128, 87, 105, 148, 197,
  292, 312, 269, 331, 35, 54, 13, 78, 219, 428, 209, 242, 362, 405, 382, 343, 150, 107, 85, 126, 178,
  172, 217, 236, 195, 336, 359, 381, 400, 100, 144, 166, 122, 264, 314, 435, 287, 8, 53, 72, 31, 328,
  237, 194, 175, 214, 360, 337, 399, 380, 165, 121, 101, 145, 434, 286, 327, 272, 30, 73, 50, 11, 309,
  196, 235, 216, 173, 379, 402, 338, 357, 124, 164, 142, 102, 335, 267, 308, 433, 52, 9, 32, 71, 285,
  215, 174, 193, 238, 401, 378, 358, 339, 143, 103, 123, 163, 307, 432, 293, 330, 74, 29, 10, 51, 266,
  96, 118, 140, 162, 260, 282, 304, 326, 4, 26, 48, 70, 168, 190, 212, 234, 352, 398, 439, 375, 416,
  161, 141, 117, 97, 283, 263, 323, 303, 27, 7, 67, 47, 233, 213, 189, 169, 438, 374, 415, 356, 397,
  120, 98, 160, 138, 305, 325, 261, 281, 49, 69, 5, 25, 192, 170, 232, 210, 419, 355, 396, 437, 373,
  139, 159, 99, 119, 324, 302, 284, 262, 68, 46, 28, 6, 211, 231, 171, 191, 395, 436, 377, 418, 354,
  24, 65, 1, 42, 112, 153, 89, 130, 200, 241, 177, 218, 288, 329, 265, 306, 376, 417, 353, 394, 440
]

def mols21ACInverseKernel : Fin 21 × Fin 21 → Fin 21 × Fin 21 :=
  inversePairFromData 21 (by decide) mols21ACInverseDataKernel

set_option maxHeartbeats 0 in
theorem mols21AC_rightInverse_kernel :
    Function.RightInverse mols21ACInverseKernel
      (classicalPairMap mols21A mols21C) := by
  decide +kernel

theorem mols21AC_orthogonal_kernel : Orthogonal mols21A mols21C :=
  orthogonal_of_pairMap_rightInverse mols21ACInverseKernel
    mols21AC_rightInverse_kernel

def mols21BCInverseDataKernel : Array ℕ := #[0, 65, 41, 421, 260, 325, 284, 303, 100, 164, 123, 145, 340, 405, 364, 383, 180, 203, 225, 244, 45,
  83, 22, 423, 42, 305, 282, 323, 262, 143, 121, 166, 102, 406, 341, 382, 363, 202, 183, 245, 222, 2,
  24, 420, 44, 20, 324, 263, 304, 281, 165, 103, 142, 122, 362, 385, 342, 403, 224, 243, 181, 204, 64,
  422, 62, 1, 66, 283, 302, 261, 326, 124, 144, 101, 163, 384, 361, 404, 343, 246, 223, 201, 182, 21,
  268, 312, 334, 290, 88, 153, 125, 425, 348, 414, 370, 392, 168, 213, 232, 191, 8, 73, 32, 51, 133,
  333, 289, 269, 313, 167, 110, 427, 130, 413, 349, 393, 369, 233, 190, 171, 210, 30, 53, 10, 71, 90,
  292, 332, 310, 270, 112, 424, 132, 104, 372, 390, 350, 412, 192, 231, 212, 169, 52, 29, 72, 11, 152,
  311, 271, 291, 331, 426, 146, 89, 154, 391, 371, 411, 351, 211, 170, 189, 234, 74, 9, 50, 31, 109,
  96, 141, 160, 119, 336, 402, 358, 380, 176, 241, 209, 429, 16, 60, 82, 38, 256, 321, 280, 299, 221,
  161, 118, 99, 138, 401, 337, 381, 357, 251, 198, 431, 218, 81, 37, 17, 61, 278, 301, 258, 319, 178,
  120, 159, 140, 97, 360, 378, 338, 400, 200, 428, 220, 188, 40, 80, 58, 18, 300, 277, 320, 259, 240,
  139, 98, 117, 162, 379, 359, 399, 339, 430, 230, 177, 242, 59, 19, 39, 79, 322, 257, 298, 279, 197,
  344, 409, 368, 387, 184, 248, 207, 229, 4, 69, 28, 47, 264, 329, 293, 433, 84, 107, 129, 148, 309,
  410, 345, 386, 367, 227, 205, 250, 186, 49, 26, 67, 6, 335, 286, 435, 306, 106, 87, 149, 126, 266,
  366, 389, 346, 407, 249, 187, 226, 206, 68, 7, 48, 25, 288, 432, 308, 272, 128, 147, 85, 108, 328,
  388, 365, 408, 347, 208, 228, 185, 247, 27, 46, 5, 70, 434, 314, 265, 330, 150, 127, 105, 86, 285,
  172, 194, 216, 238, 12, 34, 56, 78, 252, 274, 296, 318, 92, 114, 136, 158, 352, 417, 377, 437, 397,
  196, 174, 236, 214, 76, 54, 36, 14, 316, 294, 276, 254, 116, 94, 156, 134, 419, 374, 439, 394, 354,
  215, 235, 175, 195, 35, 15, 75, 55, 275, 255, 315, 295, 135, 155, 95, 115, 376, 436, 396, 356, 416,
  237, 217, 193, 173, 57, 77, 13, 33, 297, 317, 253, 273, 157, 137, 113, 93, 438, 398, 353, 418, 373,
  43, 3, 63, 23, 131, 91, 151, 111, 219, 179, 239, 199, 307, 267, 327, 287, 395, 355, 415, 375, 440
]

def mols21BCInverseKernel : Fin 21 × Fin 21 → Fin 21 × Fin 21 :=
  inversePairFromData 21 (by decide) mols21BCInverseDataKernel

set_option maxHeartbeats 0 in
theorem mols21BC_rightInverse_kernel :
    Function.RightInverse mols21BCInverseKernel
      (classicalPairMap mols21B mols21C) := by
  decide +kernel

theorem mols21BC_orthogonal_kernel : Orthogonal mols21B mols21C :=
  orthogonal_of_pairMap_rightInverse mols21BCInverseKernel
    mols21BC_rightInverse_kernel

theorem mols21A_latin : IsLatin mols21A := by
  unfold IsLatin
  decide +kernel
theorem mols21B_latin : IsLatin mols21B := by
  unfold IsLatin
  decide +kernel
theorem mols21C_latin : IsLatin mols21C := by
  unfold IsLatin
  decide +kernel
theorem mols21AB_orthogonal : Orthogonal mols21A mols21B := by
  exact mols21AB_orthogonal_kernel
theorem mols21AC_orthogonal : Orthogonal mols21A mols21C := by
  exact mols21AC_orthogonal_kernel
theorem mols21BC_orthogonal : Orthogonal mols21B mols21C := by
  exact mols21BC_orthogonal_kernel

theorem hasThreeMOLS_twentyOne : HasThreeMOLS 21 := by
  exact ⟨mols21A, mols21B, mols21C, mols21A_latin, mols21B_latin,
    mols21C_latin, mols21AB_orthogonal, mols21AC_orthogonal,
    mols21BC_orthogonal⟩

theorem hasThreeMOLS_21 : HasThreeMOLS 21 := hasThreeMOLS_twentyOne

end LeanCo.QuantumLatin
