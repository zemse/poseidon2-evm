import Poseidon2.Spec.Minpoly
import Poseidon2.Spec.DiagCheck

/-!
# The internal diagonal for t = 8 is the first draw passing the script's check

Draws 0 .. 29 fail `check_minpoly_condition`: the characteristic polynomial `f` of
their matrix `M` factors (`f = g · h`, both monic of degree at least 1), so the minimal
polynomial of `M ^ 1` is not irreducible of degree 8. Draw 30 passes it: `f` is
irreducible and `x ^ i` (`1 ≤ i ≤ 16`) lies in no proper subfield of `GF(P)[x] / f`.
Certificates written by `scripts/minpoly.mjs`, checked by kernel evaluation.
-/

namespace Poseidon2.Spec.MinpolyCheck.T8

open Minpoly DiagCheck

/-- Draw `j` (`j ≤ 30`), as `DiagCheck.drawRow_t8` gives it. -/
abbrev rowOf (j : Nat) : List Nat := ((diagValsT8.drop (j * 8)).take 8).map fun vs => vs.1 % P

/-- The monic product `g · h` without its leading `1`. -/
def fOf (g h : List Nat) : List Nat := (mulL (g ++ [1]) (h ++ [1])).take 8

/-- Draw 0: `f = g · h`, `g` of degree 2. -/
def g0 : List Nat := [0x266e61cac3837966d5cac5756cfc5dbb997197ebc775c9e13e49aa4001967f70, 0x21396ef2a4b1eccf4465b640d5227b39a4b66d6e4feec01909f0ed31d073b873]

def h0 : List Nat := [0x11ed6f0eb01e9dec1188c3e5e84399bbfd021d873b97dffbb03c60221117f0fe, 0x1dccf5df0d2062304eeb50a1e2d9097961435a2508d347c7b89874ee6dc158e1, 0x3883779eaac09ba763487149516c6432b3dd8513329ef9dccc0fe971d5c471b, 0x36388ffd6d357181110fc68db2d57ea368fbd71ea9c2a69bd2b57ecd64f2173, 0x875081113e21fb1cf0befcb3acf86bf1336106db4cfa9bb7545a9f23762ecab, 0x1627affc2ce6e04ca8a3767ceff127b9ae690095c9a03cec66cba038be3c61a]

theorem fail0 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 0)) :=
  not_minpolyCondition 8 _ (fOf g0 h0) g0 h0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 1: `f = g · h`, `g` of degree 1. -/
def g1 : List Nat := [0x2f3156f073841b32d5bc1855a2fe0b2fd2823f3df10c7af20717bbaf2dd9317b]

def h1 : List Nat := [0x30273a0c510ff45aac5a55dbb543684c2fec5dac0d7b4449eebcab028f104b78, 0x2718c0f438e403921241ff68e37f42a57efba78599b7b2157276cac33fc24d8b, 0x2c99897c34c375801769b30606cf93b4f3c7cb9690fb24c3bee1ac337ac9adc0, 0xf87cdd80d9228ae52845747ce5cdcbd2e9c58b5017ea376976065cb29b1687f, 0x1fb79927df1e7097bfb90f787b794548c9233ce0ddc2e661eba4269088c81711, 0x10c8217601cb489a2ba050751024c6b6b63e0a98d130d5708992591fc91684f8, 0x26a9848a859f4265871c295987153f5500f9acbd489e8f245613c5a333417901]

theorem fail1 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 1)) :=
  not_minpolyCondition 8 _ (fOf g1 h1) g1 h1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 2: `f = g · h`, `g` of degree 2. -/
def g2 : List Nat := [0x7cc745ecef268a9744b2cc80b94103c936c1986feec3328a728d77240bebbd9, 0x1a878e5fd118c045ce4602b8edc9c6951e140fa91a90708ba68a50034fcd4475]

def h2 : List Nat := [0x29c714c6ee45590f0659c171d3a94050041467ea1c5a5a7dbd848356d93d7dd1, 0x2f49e6753a888c7a231e6f70093997efc4342e4c4cd6fdef15257f514ce2a9ae, 0x4b54339e027ce78fd3440ffc8c470dd7193a0d2ecaee8814a12ec0d4ecb5324, 0x15cb1a11be18a14f49a35a7c0c116bb04e789a5a464085f69bbfe3e4fbe5d621, 0x856667eacaa36ebbc55528248745839b3c6fd6c3af1a360c4996bb79ea220d1, 0x232dfbcc024e2ed80a81a69fecd1b2160bec7cbb5ad6e65ebf84bc2f7a223090]

theorem fail2 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 2)) :=
  not_minpolyCondition 8 _ (fOf g2 h2) g2 h2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 3: `f = g · h`, `g` of degree 2. -/
def g3 : List Nat := [0x866633f89d66fe70e16d515e273de7c8ec5de72b7766b2b8a72beebbdd3743d, 0x19ef51c41e485ec9db9d2787c7cc04ffd58926f4d06cbb616358bffecf06735e]

def h3 : List Nat := [0x1a325ca1c170a85ec1435e430b0c7ea1033e35eeabca34dd584ac217f9072309, 0xf2690cad7c204269115ba6fbcec4af71e450f4b36d6978f66bc9799777a7328, 0x22499e76221935b388a5daab35a7ffde99b1bbf3ea80c880d26aa65ebb8c8e9a, 0x87d860eaa752bbeb62a9a5513041feb96fd9eea9290ebf2142b6d2555cfbfc4, 0x2e1073888bafdf274b620828d56a3fc4596c392bafe45da57176c2ec34f85dd5, 0x21e76cc469d78548db0996ff8215e9b7a5ceb0b62406d59b4c34a774c236d709]

theorem fail3 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 3)) :=
  not_minpolyCondition 8 _ (fOf g3 h3) g3 h3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 4: `f = g · h`, `g` of degree 3. -/
def g4 : List Nat := [0x16c5e0e5be7ea61211d6d66dc67d0583fafb2ca9964f6c07ac35561dada3610a, 0x1bd0692a9cfacb025c289e7769f33aeac6dc2c2c5c9bd928387ad7faa3c9b712, 0x265a00dcaad5357c64e645b6e1973e33e9b9c69bb4e625492c20d3cde2f851b5]

def h4 : List Nat := [0x1f82be55f67918d36e2c5a69120b296b7824b2829e299b8ce161453ac5b33ce7, 0x6999bab1ba5c17d5f3d18ebc967c124c9ac4af420b1f7f92d199cc0ed74ffc, 0x277197669f0833ac2adab283855d3c4aef248c84ad5e8de07ade37c3a8e3ec4c, 0x1cfa422980548113514c08c3b299ba750587d55e8edd9168ae6a6f9154be57b9, 0x1f4cd1aa950a4bdb56b56e780640f72fd4035387c4e6cf2e690b17dcd4176694]

theorem fail4 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 4)) :=
  not_minpolyCondition 8 _ (fOf g4 h4) g4 h4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 5: `f = g · h`, `g` of degree 2. -/
def g5 : List Nat := [0x1eafd28106e1a48b211d45e883afa7ed8af462af2cf1ef46dc2ae5095b540789, 0x20a9ed552d4c934d3d87bc5459a65be87216e264af7ca2d7f4426dc659551e79]

def h5 : List Nat := [0x1aad4df029d40c4e4189342931d1375ba568605fd4ef6bfc3c802e88b60126e, 0x23c295c8174a179bd9e28135d09ccf400917856aef21afff8f809b14542585a3, 0x17d0f9b1afec015e9001055ae32845ff1c2a90e393469f1c51eccd85bbb7c01f, 0x18508a5878b221ea2ce18cf572e96740c1e218d86cfb1ba1a125f3c7cc655cee, 0x22d359cd8b3a88f422d57cffd507764b91e2cfaa57c0ecad0da3d3d8ad764b67, 0x342d50ff88156d2759edcbb16c1a2cfa66575a695f1efa22df38267ffeec509]

theorem fail5 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 5)) :=
  not_minpolyCondition 8 _ (fOf g5 h5) g5 h5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 6: `f = g · h`, `g` of degree 3. -/
def g6 : List Nat := [0xed62896dc70dcb89caa7e15f1d59bede89308c0e7b9beae1a756a6cb3a0b247, 0x7aabce6a7dbbafdfb0938565e209c9cadfdcb1206c4d06b9a94f8830076669f, 0x2fbd962af4fff5bd285766bcd0c7a218160ed96af13f43db2ab39ff159de9da4]

def h6 : List Nat := [0x10211cfcaa59b0d56a629a41277286847971a786be98fe3835ef003cc0647346, 0x2587e29a7ff89a09117ca03948355b6dc1e525a33aa16e2dfc40e024f2a2d01, 0x2b275c8373303ab3436e2324fbc818017e02cb19d7925d71f7f5e267a3b08441, 0x239e5a05fb830fd581c01702b2c0bf0b0d1b1feee147f30ce6a44d1c34456348, 0xee3d2e4cbfb90dd79d5b299d2776a4723e4afa06f2bbc725ef71b463c86e0ca]

theorem fail6 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 6)) :=
  not_minpolyCondition 8 _ (fOf g6 h6) g6 h6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 7: `f = g · h`, `g` of degree 3. -/
def g7 : List Nat := [0x200e058a30ef8b7b80e6789cd6bf3197d1e67269e8e08065e79877d34fae288a, 0x33eac25b2f9279a6e7a54ae2bfd26f716cf975bb491785a392c878683713b09, 0x27279e759f4b8d349857abc5b34d9f4dde664b6f7af4fd3eab24a7ecc3007198]

def h7 : List Nat := [0x1e5709e6f0ef5939fe96bc652405b298d517d05726a4150ab977e14798103e5e, 0x2dcf146b2caab46f303418c19357af0fc9266a91f3540ffdbca791d7d641c28f, 0x10f7009484a0c80a2539b880fdbfc5aadaf55e8385fcf58600da067e0ff67982, 0x284720791714655f652661520a32a0fedbdef9bb981871ac2ab593d2a4a6c7f2, 0x1c0f5d5e68dfba9be52d8d8b7ae419113b1a7d2ee278a6e9c6f354efbbd9adb0]

theorem fail7 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 7)) :=
  not_minpolyCondition 8 _ (fOf g7 h7) g7 h7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 8: `f = g · h`, `g` of degree 4. -/
def g8 : List Nat := [0x14b93f4e6bc99646bb37e72751949b4bccc278461d192016d7d7eba528eb89fe, 0x2b2d9e4e50ebf5b83d405bef9936e16b0d07df289fa9afc60d5923f1008c6ee9, 0x2e5c8ae4799dfe7ee1cc74682fb580ad58bbd8b155410c2fa1c7cd39ed8c9225, 0xb5bf5606d1f1a840ac7ecbe49b6c1de6e6cbae34736f16d05da20c61544e9]

def h8 : List Nat := [0x1ff354b84eec2ccc0ced54818ca892749f3870d2dfbb8e793836fa3b0882830d, 0x4f9bb3f20f74d1e15e0bbbb8a08a2f47206f174d5dc4fc8219b1141c1b0a61a, 0x187fa3fde931c8b90fa78840e2a3e713adc8d0dba4e9b8e2f1a6bd1f4811626a, 0x1ace4377c70fa35bd7ffc80cf467f1b375dd20e5a06d2c3454d8d6fd4e2a1e6a]

theorem fail8 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 8)) :=
  not_minpolyCondition 8 _ (fOf g8 h8) g8 h8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 9: `f = g · h`, `g` of degree 1. -/
def g9 : List Nat := [0x7e6b534f3d7e25e1560c966933febfcffca1223ba83cca748534a4fc94e5f59]

def h9 : List Nat := [0x2fb3b3fa08dd7cc9becb2b337d0c584e8a189c10938c82605c5720553d76361, 0x1f19dc21963ecc9d7f3e6b6cecade855c22c655f9e41ba2e8fc1b303c7fd26dd, 0x156771fddd38a6333816ea3fbc76740f59f8baa479510b052758e7e236343204, 0x28b23d5aaad7cf90051b084cf294d2647d2049accb73cc8858fe7a0846f73dbd, 0x305fcb4934488c4512fb938c5df5123b6ae25de1bb868b8c124e241ae225546d, 0x29bb3a611cc01c49309d6bb88f8a6819ef932b20efde038c2d973a0f3f6b8602, 0x2b1dd3199436d2c547de4075e03dddb9943a9ccd8bce89a68a5541d683208cd0]

theorem fail9 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 9)) :=
  not_minpolyCondition 8 _ (fOf g9 h9) g9 h9 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 10: `f = g · h`, `g` of degree 1. -/
def g10 : List Nat := [0x12a6ff65b76ce7e15a80c3644e95f235f024b872f9f5db175651a99432bfef7e]

def h10 : List Nat := [0x15cecc244677c8305527b93e0486aba1df58590e465184fed06601f91fc45a99, 0xbb5435c74399fe24900b18daf72a5a9d86c681c0357d6f68b4d384f9a0f3c25, 0x49dcf9e3ef6834835cebd8b5f6e37f26d934c7f97b408d48656428098b61c58, 0x3d1ead0f06f10f378fe9fd4a438e9f88c01151963c291b3c107dbf93679ae3b, 0x7e3dcbb3c443d7fd23ebef18a43c17a0262ab7a0d3ba827906ff6af87b0d880, 0x23cd6bfbd186901358b186e8364ab8a1f3d3307f3e86325392235f42e0e1132c, 0x5fd3a4dae772a69b3851b967c38225a74855e5c28671604859428972cd4ece6]

theorem fail10 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 10)) :=
  not_minpolyCondition 8 _ (fOf g10 h10) g10 h10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 11: `f = g · h`, `g` of degree 1. -/
def g11 : List Nat := [0x22a1661e1b7b9ced1a90a017dd135775a23e991181b698603bb86b0c7a1a16b9]

def h11 : List Nat := [0x187b52488267c3f5ea626003b26fff06132375d06a006ad119ccc6ba552239ce, 0x1996b49b91204d90ff5acc3e0eb1e7468a84682fce5747d705fbc17541745d79, 0xfb0dc2751bc1d8eea0816bcdfa7a4097cb915a7f5281289a8d5a3c39f147c0c, 0x1889121849478a17b7f55a9c01f219512579e863cd7002fef8408c9ffb0f15b5, 0x1289b725e5f4ce8d3c09f54cabac2ff20a5238fd87e8ba45061566718e86cf37, 0x842e961d2a5196717291d9a998377660bf0eae8a728e1f417c057ddd61cfad2, 0x28b401d3fb6138d3fd710b7030d8c952634f3d01dd6197d10e67bde20b2b5e2]

theorem fail11 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 11)) :=
  not_minpolyCondition 8 _ (fOf g11 h11) g11 h11 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 12: `f = g · h`, `g` of degree 2. -/
def g12 : List Nat := [0xb45e53240baaace60a63840e3ad344350bb827d90e3a32a448c28a52763909, 0x7c95bb5d5aa31029c320827818033dc01f0826ae1dcf0c8e6739b78cc7402f7]

def h12 : List Nat := [0x13c5a848de2eb079619ddece4fa9bef519520ef24457ee6100fe543058a5cab7, 0x2c6819c16cef19d235caf79586cf6bdf6f250682dabbf9fbd75b2e964d3dcd7d, 0x2a408ea0805bebd95fcc8c528cd574a19436a055f625ec7a62f5248707fd2e9, 0x252a5757b6affe16cda2316ed0099fd60722b11d6ea2f79c75d98e567bcee8d5, 0x14e465df492525b0243daf1c3ae346828f793aa028d37965aaa3f669d6d99182, 0x2b84dc0e8b15bc4158f87c09ddd180e855261ff01f52794efb6ecd9dd624e4a6]

theorem fail12 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 12)) :=
  not_minpolyCondition 8 _ (fOf g12 h12) g12 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 13: `f = g · h`, `g` of degree 2. -/
def g13 : List Nat := [0x1b473af7108ec283010412ae7cf460a994670a0ba5f26c57229421bf23956518, 0x16602d608d999b805f976515533199ec54384c7721542f678413100e4952ba49]

def h13 : List Nat := [0x25bab18ff2422294dc8653dc50ef387cbb2ff3a486fffd3c11c6529cb0830538, 0x1f2027a5725cb2ac5815887e193954068c2ff8e153252091cdf50570246aa493, 0x3498373db5f9864525e6123988be4c222f1178c934c50378def6d06ebb16e23, 0x193c7f587294b2e1fe53637f97ac8891bd0b7f3448d6e17bd36d464f754cee1c, 0x233784e807f82acd59caaebc850ea64b51158842e500c026d009f7b01adf67c0, 0x75e1257b29a4916af737d66eac8d6ccf909aa2b50e22cf6a8bf2dac473dfd79]

theorem fail13 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 13)) :=
  not_minpolyCondition 8 _ (fOf g13 h13) g13 h13 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 14: `f = g · h`, `g` of degree 2. -/
def g14 : List Nat := [0x21d1d2a9ff7a32f8e35a705cf2372a758e299c1d0567514f2d6805ef8d98cd7e, 0xbc7975d9702f504b5c886d06a95650053f6a274ef2feb2b7cb1ded56f21fc42]

def h14 : List Nat := [0x12dce989b37ab54c73d8ae32323bbd4acbe4ae9c41eb05bb20a54c7c2da1ba47, 0x287804cd027bfe7f4e9c0e8e5c052b2b907f9ad25d84c5b04ed460aa12635b29, 0x171fbe5d9af19ebbe85a1d0facb2e544ba7caa364322c32467178b3a296dd74b, 0x139fdf10852d18c08dabe0009ee39f3030ab488d6577bd68a5d44a4d58911b0f, 0x1346745294c2b6f4178bbbe345a00600da3137569f7c638eac3e2543f4f88034, 0x1df5b1dea76e190e28179e4356582de0ef785414e34623e3ae8b9a0f345a058a]

theorem fail14 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 14)) :=
  not_minpolyCondition 8 _ (fOf g14 h14) g14 h14 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 15: `f = g · h`, `g` of degree 1. -/
def g15 : List Nat := [0x2ef76a154a8c62f86f4d06411c8e9ede4e54bb19c8276a670dd9b9b5cf45597e]

def h15 : List Nat := [0x279a43717743058247ef6041282eeea8398e360f71c601f65280aaa814396364, 0x6d8e2bb189872c520ea19c3f6245e59b34abb0c578731de6f55e99b80b66de4, 0xea900b3046821ebbbaecfbcc48053db8602a104caa7234e81393b1295b75c8f, 0xafd456fe985026123cc5793c0b558fa7c7d9041f40b0ab2a64605a8acd684b1, 0xbfaa5526af8327aab7c282cab608b033b46e9b529cba8f18ffee365dcadd77d, 0x207fee4a9fef9a30992e461a56e65364904dfb88583e7f15bdd31463bbb94a18, 0x20cb4b6d1b3154c9b16715d19d25f7151ac419c83abee58b9a62bccb86870d44]

theorem fail15 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 15)) :=
  not_minpolyCondition 8 _ (fOf g15 h15) g15 h15 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 16: `f = g · h`, `g` of degree 1. -/
def g16 : List Nat := [0x1dac6f027350856ba0693ea24a1d3912f0263e12ba9dc7b1131548b21ab9b16f]

def h16 : List Nat := [0x1a307721344690d4e2d2ec6c01c5f48b471d3462ca0f7b1ea2c55e502fcd3050, 0x974642b4f606a607aecea5b7277006182d088226db8b0f5f0e59e66289f350a, 0x2a4d74534688d712cd7d2d5a84da70a238efab176e2bcac327002d5ed9ae727, 0x26796bc2e0e53d63fa36c1e22e3832ddfdfb466781cebcace41f5d6d0b9374d2, 0x27042fbf12d0092e192a15104337e2bfec418896313660818401d65c47ecb0be, 0x277704577546476e111d98365fdb0d0829a8cbf2c73896922faf4a8de7fe6431, 0x2db8bd5101e7d91b843421f5c816f70421be0fe40bec4c7562d52ffd569f07da]

theorem fail16 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 16)) :=
  not_minpolyCondition 8 _ (fOf g16 h16) g16 h16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 17: `f = g · h`, `g` of degree 3. -/
def g17 : List Nat := [0x15cf597fbfd0dd3e40e8b725a8b49d6060e865cc1dc8fc4cce1c348759fbc8b9, 0x81daf831e9c4daa24be4e062d1f6996164f31b3501cd8c3ef606da46d597521, 0x26f81a00843e38fe4f0510baea10a1dd2537ede4056237105d6716d66f1ce2a1]

def h17 : List Nat := [0x780776cf301d978b5dfc7714a4a1bbaa82014a944248d22412242a85c66313e, 0x2ad5615fdffc20e3bf4594b373da555e6e01fd5ae82b72855928b12643424b4f, 0xe02f771667e98cccef3e306f3a0b7d29dda4f7698fa0806d67d2fc3dc8a6fdb, 0x1e6ef83161beb110c570f79db1ce3ce1a11a0830180a611167141168dbd35a93, 0x52000a2052ef652208319c7af8fd7aab3492ed6c7f161332541dba63f3f6682]

theorem fail17 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 17)) :=
  not_minpolyCondition 8 _ (fOf g17 h17) g17 h17 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 18: `f = g · h`, `g` of degree 1. -/
def g18 : List Nat := [0x2586b1479772333fc4b3d5a39d6a24fead3ebd8a32d535e5e3a9f9bd4e8c9bc6]

def h18 : List Nat := [0x56f4450bf4f3ef4dc444e5e730f0e9807f755e715916021db6fbbf7fa5ca9f5, 0x1d486e9434de6d2e517bedc5e65fa8f3efc6e30e7271375fe5866e3813d67a85, 0xddd6f8323d82c83bcd4e8747def9bfd8bad8561c23915e91dbe7123eb9a68a1, 0xb181e814d605575e232179fb8fdd10211b9fc328c00092c335015121a3c081d, 0x223c7471c714c321f5d4b23673f3ac2bc8a6549f865e7dafbf48aeaccae358e7, 0x135a58c6d19416c153a6867afb688d1ed3291719dd4a48f39389789d9f83c996, 0x1147ebd99c5e494b0f51662c7bd470297f6002797b7c15ecddb1a63b92022839]

theorem fail18 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 18)) :=
  not_minpolyCondition 8 _ (fOf g18 h18) g18 h18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 19: `f = g · h`, `g` of degree 1. -/
def g19 : List Nat := [0x232db6d4a4d1c3043e537751f131b1bfc51a5ed71d39bbd2a18ebc0b648e9bca]

def h19 : List Nat := [0x1a089c758d1d69ff5565223b0fa8d622a26a8b89775b5a2e7ac45081a12ab9f5, 0xf2431b76e6181535b04e97479926ea60ba9891d306d0615d69df2012aac91e4, 0x192bdde79527499d40cf0f6d499873eaabbdf3bc7d8ddf39949fc7a2a58334d, 0x2d855990b90b88d77a45defcd92f128420c83955c450428f93e6d2b0d5aa8d02, 0x2bf8ccb5c1b8224072bee627b6289f144c71d574404bfc6889f3db432cdf6015, 0x2d7b71a42daab411f8b3866a069971b96d081558c1c33f979a249a093f54fabe, 0xb36e93c534648ec7c5a3ab287513ebf05177225596af84b879090fca17f2f4d]

theorem fail19 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 19)) :=
  not_minpolyCondition 8 _ (fOf g19 h19) g19 h19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 20: `f = g · h`, `g` of degree 2. -/
def g20 : List Nat := [0x1f3b3fff9c2971761d10fb055c5beaa52ee22aac35566eedff642486c803236d, 0x1d923a67a614677befbc4164f3ab1b0e1fc065c40063d4f6ff965a6abd7dfeab]

def h20 : List Nat := [0xb2f5b0ae80494519b00f5a280e92b2449cb8dd012aa43d94f8ecb0c2b0e6231, 0x26729f7d33642eeb8043a58c3ee11451b97aad303eb98d6e671b2ebce1b7b47e, 0x12988fd14a091de1a147598057f0423d7b8a378b8bef30177ddf1f9c952b4d79, 0x1f4a26214f520e8e9e38a1357a3bdb9035fae392766f5eedeca3442adb17580d, 0x2f8be88a3107f81a8f26d51ecba7df7019fc9226a056d2e873db818a2f1bca0, 0xbd4a059dff89863eb7404d8a2033da1fd5163b08812cb93247d06e05f1a147e]

theorem fail20 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 20)) :=
  not_minpolyCondition 8 _ (fOf g20 h20) g20 h20 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 21: `f = g · h`, `g` of degree 2. -/
def g21 : List Nat := [0xce8d22f288f40f4383103b9b9b590af15736a2c990041f4b1f7a99860df4cbd, 0xce58533b09c222c481eaf4d12d8dc1e490bfeec7500920ba4f5d0c9c987d8d5]

def h21 : List Nat := [0x5f2492c581b358616cd9607d50a0cd07ec3aa8c941c65dff228cedd6342a313, 0x45669b0b0f6b0c63dc96c3d2f26f9d08d7cded46d01966328db25fb73da729, 0x2200479e6ac8bd7ee5882a5f0c1c8e90733666ba67f2cff551077ba4df64e67a, 0x15396baab0d3130efec2a50ae218266f40a14abf0e885c26d345caf3b511ebbb, 0x2f233ff27e12c8a3943f4c610ee012c13ae99e684d646ffde346017b318f9358, 0x24b92bef6154820f8af76609e44ad0b21d5c11011119609e109a2c2136cbde67]

theorem fail21 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 21)) :=
  not_minpolyCondition 8 _ (fOf g21 h21) g21 h21 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 22: `f = g · h`, `g` of degree 2. -/
def g22 : List Nat := [0x2ed48bdeafda90feda9c38d19c02981306064f1ab98a8ffd15f066772dbde0a9, 0x12e0f4ebba0592ac49c8df2f03400e318372323684e447fc865d13fdda981e28]

def h22 : List Nat := [0xa2bb27fb4f0f91c0e59f849161b9eaa864102bad1efc81702ddcdc0e3c6a35a, 0xe9bba88b0950088ff2689d2c48bb84ecf24172e4ef00e055c3732bd9a26cc85, 0x10e4d454e964f1f271ae53044e1678965cf2800960b1485696cdd32d7bdf76ce, 0x1c28f6e924d07e495e46ef0c940e7cc75ec4f83cbaeaa7d0538a105a908c5e92, 0x151f6aba8d7311367c98b51460bcb65575518a3a222450699ecb2afe396416d2, 0x1c0d7726a80a4e143ef0f7078a2ca12e5d10373ce34ac8de09f0110109f3b766]

theorem fail22 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 22)) :=
  not_minpolyCondition 8 _ (fOf g22 h22) g22 h22 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 23: `f = g · h`, `g` of degree 2. -/
def g23 : List Nat := [0xf12b61bcdd3cd7609a325bbce8939c2af71d85316a2232274d8086d89635be0, 0x1894d5e5dab683a1574b3b5a0f2c09f208fc61e836aac7c127504a67629c670f]

def h23 : List Nat := [0xcabec2f6aafbb3ccec66caac1d544743e396b686cc96a225f52ea9de51cf4b2, 0x28c4ad4b60cf93b6c097d28f76f810ee1a4a984e50f99ae52acd3982d5032aea, 0x1492446e2d4556395441584ed95c33c9f0d180360ea7f7afcb4d15915897a7d5, 0x1718e02de74677b5520e37181ec9742e08833aae96c1945a99895b665c21034a, 0x2498dc9a9c496bd34c446d66284597bfc8e296427f2ed65373f194707b80fcf4, 0x272273c972f2ab6b70994bf1e216da0b2064142939a021b725867304aef6bd70]

theorem fail23 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 23)) :=
  not_minpolyCondition 8 _ (fOf g23 h23) g23 h23 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 24: `f = g · h`, `g` of degree 2. -/
def g24 : List Nat := [0x16f96990cbde28029804c889a0727943c6026f452cb65a4269ebe074e56b693b, 0x1854ac2bdf8f13fef30b4a3e13782ed92b6bbafdb387e61abea5cee62b44eeab]

def h24 : List Nat := [0x65592b9a603f6b4768a26af8a630868e0bef19d7b36ceda83d0ff88f37779f8, 0x289465dac42075db1e5126047cead3092ea40ac49dfb8dfd99a974b358ead8e5, 0x245189ea48890e207a1af63a5b8935ff56b2d3df28119904ceabb5ed4ca28401, 0x2dc3d8a081b04dcaafdaa084971c0b032d91f253ce45a8746c72ae43045e5b64, 0x1837212ea6064b0d8f2d355ad5cad41c5aec56bf249aa9f40773de99ca747919, 0x21aacf55af80ac01a9febd84bbcc3d5375d51d61775c5eb041343ccd89e60458]

theorem fail24 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 24)) :=
  not_minpolyCondition 8 _ (fOf g24 h24) g24 h24 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 25: `f = g · h`, `g` of degree 4. -/
def g25 : List Nat := [0x2967b2cc22aec7c2d05a48f090b6632f67657444d06a61466df13ade35c175dc, 0x3877b66af07a025ad03e3372b5af7ec0894123b7e3c6fae629f72a0c00eafb4, 0x27b07e01b43477d7d9c946a9c286f33dbf4511e505f15903ca4c8806fc62c3c6, 0x16e1b0f228f1fb2007a69d7fede0a7ed879fc8c2eadcba31a80c574daa0ba651]

def h25 : List Nat := [0xf6c0ae6ee7ef7185f451fdd4a2defdaaabc16b630484701e2f38d19586fa12f, 0xa543aa8e1d29ffbc0d30b1b5ac8a05bd1b2d14890e0835ded05a8a9d415bd8d, 0x7a64afd1946846e56b8305e3ddae4b3720e5069850c981fe8655369f059d0ac, 0xd2275ef0561f8dce0aa506a52e0331f52b67ff6cbcdba69bb7e25dff4bb3a59]

theorem fail25 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 25)) :=
  not_minpolyCondition 8 _ (fOf g25 h25) g25 h25 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 26: `f = g · h`, `g` of degree 4. -/
def g26 : List Nat := [0x192560bb0e523d0cc06515452930a0d747cbc344cf28622a02c6dfbbaa61d020, 0x29693e380b03a8e102b1754fb75a71f2ff766083febcb643943dfc4488e00d08, 0x2490913712819b031b56e7ddb3d3daa8956d3445a5ba5f46f82310e620cee731, 0x58dc88300c0b3f9e9aee8256c980fefe65986535aea128f818e57dae432b310]

def h26 : List Nat := [0x108db36151a8d466ae311af711f5a7e4e44ae4af19ee2c79afbf9909ddc118c1, 0x2b1f5130d2e74da666995bba2e925bfdf53340d9740a1d88bd56771b94ea429c, 0x274d6ff4e2b6a489c734651d239feda5ad3a62acc9ea1942f2fcbe6eca3a7eef, 0xc80456c7d41f7a48dff3f7eab330048b162d4754813b50fcebbe36d9ac8c15c]

theorem fail26 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 26)) :=
  not_minpolyCondition 8 _ (fOf g26 h26) g26 h26 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 27: `f = g · h`, `g` of degree 2. -/
def g27 : List Nat := [0x59872ab9749e104058a326910d0e3b2063e57ca836a0f64728ccb3f77828fd0, 0xcd4951265afde9663f3027d31337c84d654e2b32e420d9b8e06134247386462]

def h27 : List Nat := [0xa991614129048ee6e170521c3e087e48fb0c10caae4bffc8828dc1e15f1ad47, 0x26be189d76009d146f0e8d7ac4e91d9509a80bed607c75186a5eecae6f20225a, 0x175c75e1619e3d81f3a44c192b8084ed2cd38d3c96855b515dcdd0e420b3b37b, 0x7e3cdc8f72beb242c661acd3c3b2fd0f1e95167725272cd1bf23c9c508e5337, 0x89670bab1fc532f6690e5f9d3c9227842262092cdf7f158829d425b224c318, 0x61176153aa3868705f30488b4e380db7ea08d915a1de691e2ae5a7b022f89da]

theorem fail27 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 27)) :=
  not_minpolyCondition 8 _ (fOf g27 h27) g27 h27 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 28: `f = g · h`, `g` of degree 1. -/
def g28 : List Nat := [0x51863f28309732fd1701b09fcdf6de2de8dce67b4e8e37214eec22a241ca11c]

def h28 : List Nat := [0x1532cf6d25b0a767ea8736a98a16717fbf9f8cc54ae32d6eb4c845950b7b846e, 0x2089718408dc3b716402d0df150df621d79a737085f93d3887bba3ecbe0a4e0a, 0x198cca6d8052446f23e13ce56c1d475ed106a3539e0b04a778de209623980353, 0x1f8006afc2900a7101163cf0f4d86ee67233e25960279e598758e08534b3c5f0, 0x1ae113734d0f4aeca44d96fe50158c548edc24811e65762d899dd5d2142f61a9, 0x254ce194304ede440deacd15674935b2c56b2f865e1df67340337e5e352cfd17, 0x16cf8a2940e02735eff28e60d0ff3578bd4ea99d75a1649f67392c4cfe015c15]

theorem fail28 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 28)) :=
  not_minpolyCondition 8 _ (fOf g28 h28) g28 h28 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Draw 29: `f = g · h`, `g` of degree 4. -/
def g29 : List Nat := [0x2f4e9489726dff61abf44df92fa3a1ee1820aa8f2be2eb4a3c9adfb801e31633, 0x5646b186abe3e4a26dd56b5d026bd3b78c79817fac949de45e7cf81627014c9, 0x67370e7c2ee8297a9fe42d4ecde4344b64d87bca2dd91cfa609e3a02db0577a, 0x1206c2e92c37cb5b749fcee06ccdc23d90f792657f3a6d9a1785193e4406221c]

def h29 : List Nat := [0x15db80d19096b62690519b2c2a28f7bc770103a19d36fffebaf7c72ebe3393e6, 0x1510212acd3e1f6d26d48cddf61c067fcd73e33dc95caa21fe9467df8eb18cb9, 0x1d51e9196fb78707e63f4a046d0b6faf160e54a21939b7312e9e39cc35cc8a66, 0x249b9e1f26cbbd7fb75adf8a4d9f084520cead367740b271080313ce596de14b]

theorem fail29 : ¬MinpolyCondition 8 (partialMatrix 8 (rowOf 29)) :=
  not_minpolyCondition 8 _ (fOf g29 h29) g29 h29 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Draw 30 -/

/-- The characteristic polynomial of draw 30's matrix, without its leading `1`. -/
def fl : List Nat := [0xe0855578c2cc940aedd5853840c97f19a68b02ab85b98d5223d6e360a93d3f, 0xcf2318ebccec1b77ba801fbd574d0c2f6596f73bb55876c4193060e7c04a9ec, 0x9ce7d8ec1d002a810ad883eb0d2c6bf014d4f959c52e9564b1592396689390d, 0x2bdc0493528e8b48177386060bf0f603630e179d7b49e8625967f035f90a822d, 0x123addf800c0343a055bdc6dfce782ecb13dc5c76416647692385e1391f4a506, 0x8e2a5686a64193ccab169bc408b0dd0a8909e446162db5f873987505581ea6f, 0x3a77e53251f359a16569eed64dd12fc198ce88111f1062fd47769ae32cc56fe, 0x10234a1534888a1ec81fdfc41ece986b6dbd4a7e46c047bcc34277ef898f847f]

theorem mat : matOk 8 (rowOf 30) fl = true := by decide +kernel

/-- The bits of `P` after its leading one, most significant first (1 part). -/
def bits0 : List Bool := [true, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false, false, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, true, false, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, false, true, false, true, true, false, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]

def bits : List Bool := bits0

/-- `x ^ e mod f` after each part of the square-and-multiply. -/
def sq1 : List Nat := [0x2b36dab3269928bcfe1a945f5cd8db6f3f34043f62553f25e1a7697dbc097bf2, 0x2d2ca88af006e268085d324333a42cb4685f895aff36742ef497d684eea4591f, 0x2745806789c588f210f226298cd4d5a1a612bcf4b4afffdc42275972409d8aab, 0x2f33ad10aa68b4b7bd30a2d605e7d9160c6ed376d6c97af7fa11b36e80d1e113, 0x4634d5d35e1cdb709a791ddec19e72acfc9578bf51bfbd2e4243acbd5cc939d, 0x248146b6ae637d09f9b99b33721c13b4af8197807e0abfc17e26710655a11ac8, 0x8f4948454d795aef6a9ec2f22fc2051a6e3d66463cb43348a06328a7abea562, 0x2beaa59b10e78f8ea31155eb7a0e96c8890358cba8bd5655766c46cd52551cad]

theorem run0 : sqRun fl bits0 (xL 8) = sq1 := by decide +kernel

theorem run : sqRun fl bits (xL 8) = sq1 :=
  run0

/-- `x ^ (P ^ d) mod f`, d = 1 .. 4. -/
def H2 : List Nat := [0x2c25b194bef255003710068b69565056c2e8cff554ad99a5908738fedbdddd75, 0x60a82e606b4587b4ba57069d6483935e7713db50ea2542b6d6d94dde80c4dfe, 0x244574c8c87411d606b5241b369c7441679d120b6b7e3a28f42629dec351b51e, 0x22665cd3f128958ba9e8d1cecc2c509f2a7da5b6c0f15ae613ed0bb24a882e62, 0x2854cec103941af395e7a3813c45c8e46a8448c7d3594729c99b1e48e4e612a0, 0xe08d15cd6e5eb3e8b9e9fafa2c4ecf9ef3280132481b5c25a6f7fdc045af583, 0x273a0ad1b3de0eeeaa7e12332415c1033e3899866848e467e0bcf43646326433, 0x2c8702b69a2fd0c3e3987682796b71f68b6ac0911d6af392273cacd6347a5a3b]

def H3 : List Nat := [0x1dabb36494eea26ca562a5edcd67c6f6df68ab988ddceeebac5d654e331434ea, 0x12d853de91d761724ca9f2bf824442125b435303718633791b06ba1d56b7602, 0xf717ecb3638277f8b8c22da103af756ece56c3fd7671024f9bccc72569987b, 0x16b69201461290c68177a1d5c7dbbef371f8e3ddab56aeaa8402003deff29f71, 0x2e5cefff18d9204ed3f7fc6be5729240daec8f6f8fe3b22aae89ffd1adc51ef0, 0x1bcb14e158cbecb7057abf6c3e8b6a862dfc617c4a1fd6c7cb07f44098a4bd94, 0x9a55294a2712862645a37de899a738684542c71c1d1ec0f3dda2cacc5d8be9b, 0xfaa40c98b0de1a415a2d81e19bba2ab590057e2eba789f5ac7a885f3d7db2b8]

def H4 : List Nat := [0x2c416dd6d85fa8bbbb0c6793cfde3749cffcd56028bdc33340bcf363c0a2e52b, 0x139e49d1fa2f8472ab35482dfe9e4c722e0e5ae404ba415b2b548b8b5287b038, 0x2f96eafb17594da9be0b7fcf198dcaa25c79b979a9674f817ae11687c7b36627, 0x29ef407601abc566fca2f99ad530112e61e6f78cdc21dff1bf0b888bf00e2583, 0x17b26531711fd892a2fd1899f46e3928ae893b881c36fe20cf1eac1f4cbb06b, 0x16d86b91a119a85150e693553d779c7b00e9af4432957bdf0b5053cfd0e7b21f, 0x19a9a60355ffdcc6e49cd59f1ab6f4ea95aad72757b0392b97800a1838f7a158, 0x180dab2a5fef4c4416520016f2d378294c7befc3296df0e449d106f466312b85]

def hs : List (List Nat) := [sq1, H2, H3, H4]

theorem comp2 : compMod fl sq1 sq1 = H2 := by decide +kernel

theorem comp3 : compMod fl H2 sq1 = H3 := by decide +kernel

theorem comp4 : compMod fl H3 sq1 = H4 := by decide +kernel

theorem frob : frobOk fl bits hs :=
  ⟨by decide +kernel, by decide +kernel, _, _, rfl, run,
    (frobChain_cons_of _ _ _ _ _ comp2
    (frobChain_cons_of _ _ _ _ _ comp3
    (frobChain_cons_of _ _ _ _ _ comp4
    rfl)))⟩

/-- Bezout identities `u · f + w · (x ^ (P ^ d) - x) = 1`, d = 1 .. 4. -/
def bez : List (List Nat × List Nat) :=
  [([0x8ab41aba83589885d3ff83d49dfa112c199ab187f2108c36381e55992fc3dd2, 0x2014d238fe81590a0c630db806ec136322202ef257f939f5d25f9c78fdc170af, 0x23616b4d2a5e3f512c6636531912e179749a2fe349b7e6830faa11409957ba1a, 0x24740a90e3e1fbd719e5d60430c62d6c0b38bd73e65621e22ddb7bf58c5f039b, 0x1d53c2d2748ab03689ad08d09fd4ebdad5ef508dc152c406a2bef9fbd0ef4402, 0x1e3d11d4a45399c61cc277d1cbf7de5719198f8c5693e1c5f0276f995800f24, 0x29d31fd62032a94514edcf51bc68b512662f913817ddb18dbe48a30346f4196b], [0x7983e99b6aa009775a1a1a454a1cb7d48d3fd81f46cccb6e1640ccd82d404b9, 0x89c1618b1faa88593b22281e76ba93436b9720cbcd2e0f16bfb2a40499bec07, 0x218d974f52ec5062d7ef4527c8ca56b82eb3b994f2cebe507a15b830aec630bb, 0xcef40162ebed6681a9f1487459b3999b63dcce79e72e6d97b57115d9a486c7d, 0x2f9f08d10c0e20110687022b03983d0be76edea88c7a5180a8ee87ac2fd5518d, 0x2f2b6fd278b0a54dd1514cd0c7a71d09608b7661d1dbefc85ebe00b630aaffd, 0x277f02e1aede4b648cfcca58d3fdc4d59a74e0b59049036a94bd928d0aa8338c, 0x2da573154a549b0c9032b6b0eb797377518e80c89c657a48eff84668b89d49ff]),
   ([0xbe7db8c27862031c1f7e61233b0c82822d01677938ca5622e1114ea1363099, 0x7e4101de0b0edc1ffb9082b687e583bf9cae1ac2e550d51d1e60788fdb592b3, 0x1270b16b311c441d455f7d288c6e5adeed7d92b4a81bfc9b3d73d7f1576eb77, 0x27d562c7595e0cc8e576c0575c98550f28fddc424a2786621f3bcf63dc3c017e, 0x30419cdb717dcc4785ecdb83b0c256362e58c50eb7234f54c3b14d85f0e819aa, 0x2df99de258f5205d9065243a1d2b9ef7cfa5da49d97d939a4994ca7a55a21ebb, 0xa36afba95ce303e0b8581211d83a87e754d85e8ac51045db39c7937430253b6], [0x2a1eaa4a989b281eac36fee98e34d5ce10bfc4ed5265da4023fa88cb33603961, 0x1cddbac16e6f367c5d48ee2e2e870daadf464a2d536f3880fede51fd7cc25300, 0x18d36ac21ee6647b28e5b99f57994cb45fc2b1423f894141412109618255772a, 0x2e383dca53381d798df5b6afd5eb679e8dabb7cf964dfc031d55285cd415a5ae, 0xe04057d5d1d7751811b53cc2da2bd5094342b660bf0bd658d204263a3cea2bd, 0x1a3d2ad68bb33e532be8d7ec8153fa6be3bea1b3789b035e32e79e0b3133600a, 0x195f75ccca2e18786a54c5ba21dc3b7f3d150f51ddcdaf048b724105e38364ad, 0xe936a5117d56fee3580162746429c03b71a67e39c4c069aa667ba20cc42542e]),
   ([0xe94d6fc6ebba8df342d4a070d3e1834dcb140272c379e5b054bdac2f94b04cf, 0xe761dc51ddf434a9c4f33d20393a6cbe6b3593ea5be918cc2f478c5bf13177e, 0x2b94214f0c1cd48841acc24aedd567cbf66da3823b51a96e9faf6c273fb1fa21, 0x169581c62fd5b56dd619bcde51e0236c30dc080acb85516a063a701ad53040f2, 0x1b4fc2bd31be0cd7f71f4151b8904eb12a287b27e77e80376c704fb0769106ab, 0x1060cf0cf85e143ed4d1e989d153d9878864658e916c871388805378964ce965, 0x5bb11ae2fbff539b9ae52efd3a21094a6fcf2eee26201d9b3d9c0d07db76620], [0x2ce496532487acd2ae1ed3390e6e926adca4dad9f82a516406a68dac227aef71, 0x28bfbdd9867b3f84e3492669e1ec1028d49e464b8b2e2cab87a924ff8278f88f, 0x125f972d32b2ea0363d899a6be36995557ffb271790a27185a8723bfbaca23cb, 0x1542d58c7ab223bb4bde732f7c98a1e3e63bfd7b25a7c6447fc0bb32c863a09, 0x25d756da9c9170d537be3c20f0a7457d66c258a029782ddbb811715d7c9613c5, 0x17cc011e59a08eec678334a3eea6ef1dbf6d25531b155a0597348896e420a1a5, 0x8b01f7bf3497b3be0fa0cd557133feebac4f1eb13ace95d1f3b1ec9b4706e97, 0x2f017167646a78207fbb50bd87e277ec9cbc29bda7b168b0063fce7f2076da35]),
   ([0x8c12b38694124dda25f480cb1867854b1c9886d2f496e4fe5ae71c936b9a632, 0x1bb559be3b057ca815f482c82300c617451f866a5dc38c569f6a91584b34bf0a, 0x2169b6bdb48cb1df6ff4e919f3e87a1359c8d3f118f538d8816ed69d75b257eb, 0x24201ae2b2233560c2aa3b612d58cdb65bed3dc5b42f2d4f8de2f230b8c7b838, 0x12364d8a1a05d37171b25ca33a2ca67637e6c12ef2904b8db414452d03d4cb14, 0x10cd511484f7d28848f463a4f7c3492ffb9f8ea722ccf5b0b3d22527e1eab995, 0x15c252c88496e9d48fb354040eba83adc2a10c1d38f45d5fe3b7c6b7ceae7445], [0xa9cefa22ccd32ab499fd0c984fcdea149a3fda493cb157cfe957da7039363e4, 0x1ad3ae4eb56c5a53924734b923e52f14bf5dcf9e83e54eb1b5d4b10ec38b5f11, 0xc467289ed93e3873334082dc6eb16bc191ef5fc3995e4072b01f95671085170, 0x1617e40cfe65e93133700dd68bd8ee6b8913ae8bca87d182c924cc6f1043c950, 0x152c03f89eb9926958d19960cbd44fb063e7ae0f050c165b7befb0299a4d73d6, 0x54aa7144c1fb1f72e42ed136fd02c08332be3169d20674355405adf0e0af12f, 0x83c13d61f33b5a7c6f6b39cd466437febe26bb60a65cf6b6c0512392c8ea39e, 0x2b78245a802d2dcc2165faf79b2e74f7ae01cca97141e92aeead6232a17dc8a5])]

theorem bezout : bezOk fl hs bez = true := by decide +kernel

/-- The maximal proper divisors of 8. -/
def ms : List Nat := [4]

def W4_1 : List Nat := [0xf1d124e480466db52e1a32cf1395c38913975c3f6285176931a2d02d7f6613c, 0x1931230a3d238957838af9f39f44b963251c3d2f5cef5e71ac0c0562d2d76b05, 0xe7bdc9139d769c59e7ce3d77d62b0e40458681959e68915894217e937d7f6ba, 0x2057681de0b5dcb533d57366526a32d78709ec0d4eb12bb6ee5ec30817c0916d, 0x1cf1a1e44a81845a61f78b8e13555136c1283d2459ae369e8b9f93da8ca9650f, 0x1f201058ca6f2a977befb631b4abc3896cb30c35f813cf1f32c40f08a81e1569, 0x1aca95601b72712e1bf561a00da883c06f63f87c28c75a3c9f3031dfc0699175, 0x1d10a700b0e3679f4d51ebcb167ae0f77e8936b1bc712229976062ff268ff034]

def W4_2 : List Nat := [0x2545e203f22d2daa1e505b8d67d43017c6a72cca319bd973382ef1b154272d7c, 0x1c691b9072c7dfeec79b21a6d0feeaaa24debeed1060559905779d60ac1908fc, 0x1a5aea2ed5c46015627bbde924f8b909905441683fa4f4a37b3bff211b202710, 0xd27a2934439bcd24b21e9c9910a2a730d7b11b1c99a9fbe38aa3b5ab6db5ecf, 0x1dc5435a0494762a642087723c1a8a7b8ceac95931d86b9f1dcd93e3c999575c, 0x12feb4f0dc5d808ea36777ecedce150488d01a24cb9fa69f2febef0c751ab8d1, 0x873b3c6d75d86fc88b1f9f51be952407a7c490cd0e93f6e9294b50da975715e, 0xf5026cd3555da5ac26d3dffb3fa7e642f4baf192e4e57d724715a243a557ecc]

theorem pw4_0 : powsNe fl H4 8 H4 (mulXs fl 0 (xL 8)) W4_1 = true := by
  decide +kernel

theorem pw4_1 : powsNe fl H4 8 W4_1 (mulXs fl 8 (xL 8)) W4_2 = true := by
  decide +kernel

theorem pw4 : powsNe fl H4 16 H4 (xL 8) W4_2 = true :=
  (powsNe_seg _ _ 8 8 0 _ _ _ _ pw4_0
    pw4_1)

theorem degs : degOk fl hs ms :=
  ⟨by decide +kernel, by
    intro m hm
    simp only [ms, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl
    · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, _, pw4⟩⟩

theorem pass : MinpolyCondition 8 (partialMatrix 8 (rowOf 30)) :=
  minpolyCondition_of_cert 8 _ fl bits hs bez ms (by decide +kernel) mat frob bezout degs

/-- Draw 30 is the first draw whose matrix passes the script's check. -/
theorem firstPass : FirstPass 8 8 57 30 :=
  ⟨fun j hj => ⟨_, drawRow_t8 j (by omega), by
    match j, hj with
    | 0, _ => exact fail0
    | 1, _ => exact fail1
    | 2, _ => exact fail2
    | 3, _ => exact fail3
    | 4, _ => exact fail4
    | 5, _ => exact fail5
    | 6, _ => exact fail6
    | 7, _ => exact fail7
    | 8, _ => exact fail8
    | 9, _ => exact fail9
    | 10, _ => exact fail10
    | 11, _ => exact fail11
    | 12, _ => exact fail12
    | 13, _ => exact fail13
    | 14, _ => exact fail14
    | 15, _ => exact fail15
    | 16, _ => exact fail16
    | 17, _ => exact fail17
    | 18, _ => exact fail18
    | 19, _ => exact fail19
    | 20, _ => exact fail20
    | 21, _ => exact fail21
    | 22, _ => exact fail22
    | 23, _ => exact fail23
    | 24, _ => exact fail24
    | 25, _ => exact fail25
    | 26, _ => exact fail26
    | 27, _ => exact fail27
    | 28, _ => exact fail28
    | 29, _ => exact fail29
    | _ + 30, h => omega⟩,
   ⟨_, drawRow_t8 30 le_rfl, pass⟩⟩

end Poseidon2.Spec.MinpolyCheck.T8
