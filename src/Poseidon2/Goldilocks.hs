{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-# LANGUAGE DataKinds #-}
module Poseidon2.Goldilocks (F_G, goldilocks_8, goldilocks_12,
                             goldilocks_16, goldilocks_20) where

import Data.FiniteField.PrimeField
import DSL
import PlinkLib
import Poseidon2.Poseidon2Cnst

type F_G = PrimeField 0xffffffff00000001 -- Goldilocks prime

-- t = 8 -----------------------------------------------------------------------

{-@ matDiag8_M1 :: VecDSL' F_G 8 @-}
matDiag8_M1 :: DSL F_G
matDiag8_M1 = fromList TF
              [ CONST 0xa98811a1fed4e3a5
              , CONST 0x1cc48b54f377e2a0
              , CONST 0xe40cd4f6c5609a26
              , CONST 0x11de79ebca97a4a3
              , CONST 0x9177c73d8b7e929c
              , CONST 0x2a6fe8085797e791
              , CONST 0x3de6e93329f8d5ad
              , CONST 0x3f7af9125da962fe ]

{-@ rc8_f1 :: [VecDSL' F_G 8] @-}
rc8_f1 :: [DSL F_G]
rc8_f1 = map (fromList TF)
         [ [ CONST 0xdd5743e7f2a5a5d9
           , CONST 0xcb3a864e58ada44b
           , CONST 0xffa2449ed32f8cdc
           , CONST 0x42025f65d6bd13ee
           , CONST 0x7889175e25506323
           , CONST 0x34b98bb03d24b737
           , CONST 0xbdcc535ecc4faa2a
           , CONST 0x5b20ad869fc0d033 ]
         , [ CONST 0xf1dda5b9259dfcb4
           , CONST 0x27515210be112d59
           , CONST 0x4227d1718c766c3f
           , CONST 0x26d333161a5bd794
           , CONST 0x49b938957bf4b026
           , CONST 0x4a56b5938b213669
           , CONST 0x1120426b48c8353d
           , CONST 0x6b323c3f10a56cad ]
         , [ CONST 0xce57d6245ddca6b2
           , CONST 0xb1fc8d402bba1eb1
           , CONST 0xb5c5096ca959bd04
           , CONST 0x6db55cd306d31f7f
           , CONST 0xc49d293a81cb9641
           , CONST 0x1ce55a4fe979719f
           , CONST 0xa92e60a9d178a4d1
           , CONST 0x002cc64973bcfd8c ]
         , [ CONST 0xcea721cce82fb11b
           , CONST 0xe5b55eb8098ece81
           , CONST 0x4e30525c6f1ddd66
           , CONST 0x43c6702827070987
           , CONST 0xaca68430a7b5762a
           , CONST 0x3674238634df9c93
           , CONST 0x88cee1c825e33433
           , CONST 0xde99ae8d74b57176 ] ]

{-@ rc8_p :: [FieldDSL F_G] @-}
rc8_p :: [DSL F_G]
rc8_p = [ CONST 0x488897d85ff51f56
        , CONST 0x1140737ccb162218
        , CONST 0xa7eeb9215866ed35
        , CONST 0x9bd2976fee49fcc9
        , CONST 0xc0c8f0de580a3fcc
        , CONST 0x4fb2dae6ee8fc793
        , CONST 0x343a89f35f37395b
        , CONST 0x223b525a77ca72c8
        , CONST 0x56ccb62574aaa918
        , CONST 0xc4d507d8027af9ed
        , CONST 0xa080673cf0b7e95c
        , CONST 0xf0184884eb70dcf8
        , CONST 0x044f10b0cb3d5c69
        , CONST 0xe9e3f7993938f186
        , CONST 0x1b761c80e772f459
        , CONST 0x606cec607a1b5fac
        , CONST 0x14a0c2e1d45f03cd
        , CONST 0x4eace8855398574f
        , CONST 0xf905ca7103eff3e6
        , CONST 0xf8c8f8d20862c059
        , CONST 0xb524fe8bdd678e5a
        , CONST 0xfbb7865901a1ec41 ]

{-@ rc8_f2 :: [VecDSL' F_G 8] @-}
rc8_f2 :: [DSL F_G]
rc8_f2 = map (fromList TF)
         [ [ CONST 0x014ef1197d341346
           , CONST 0x9725e20825d07394
           , CONST 0xfdb25aef2c5bae3b
           , CONST 0xbe5402dc598c971e
           , CONST 0x93a5711f04cdca3d
           , CONST 0xc45a9a5b2f8fb97b
           , CONST 0xfe8946a924933545
           , CONST 0x2af997a27369091c ]
         , [ CONST 0xaa62c88e0b294011
           , CONST 0x058eb9d810ce9f74
           , CONST 0xb3cb23eced349ae4
           , CONST 0xa3648177a77b4a84
           , CONST 0x43153d905992d95d
           , CONST 0xf4e2a97cda44aa4b
           , CONST 0x5baa2702b908682f
           , CONST 0x082923bdf4f750d1 ]
         , [ CONST 0x98ae09a325893803
           , CONST 0xf8a6475077968838
           , CONST 0xceb0735bf00b2c5f
           , CONST 0x0a1a5d953888e072
           , CONST 0x2fcb190489f94475
           , CONST 0xb5be06270dec69fc
           , CONST 0x739cb934b09acf8b
           , CONST 0x537750b75ec7f25b ]
         , [ CONST 0xe9dd318bae1f3961
           , CONST 0xf7462137299efe1a
           , CONST 0xb1f6b8eee9adb940
           , CONST 0xbdebcc8a809dfe6b
           , CONST 0x40fc1f791b178113
           , CONST 0x3ac1c3362d014864
           , CONST 0x9a016184bdb8aeba
           , CONST 0x95f2394459fbc25e ] ]

{-@ reflect goldilocks_8 @-}
goldilocks_8 :: Instance F_G
goldilocks_8 = Ins 8 7 matDiag8_M1 rc8_f1 rc8_p rc8_f2

-- t = 12 ----------------------------------------------------------------------

{-@ matDiag12_M1 :: VecDSL' F_G 12 @-}
matDiag12_M1 :: DSL F_G
matDiag12_M1 = fromList TF
               [ CONST 0xc3b6c08e23ba9300
               , CONST 0xd84b5de94a324fb6
               , CONST 0x0d0c371c5b35b84f
               , CONST 0x7964f570e7188037
               , CONST 0x5daf18bbd996604b
               , CONST 0x6743bc47b9595257
               , CONST 0x5528b9362c59bb70
               , CONST 0xac45e25b7127b68b
               , CONST 0xa2077d7dfbb606b5
               , CONST 0xf3faac6faee378ae
               , CONST 0x0c6388b51545e883
               , CONST 0xd27dbb6944917b60 ]

{-@ rc12_f1 :: [VecDSL' F_G 12] @-}
rc12_f1 :: [DSL F_G]
rc12_f1 = map (fromList TF)
          [ [ CONST 0x13dcf33aba214f46
            , CONST 0x30b3b654a1da6d83
            , CONST 0x1fc634ada6159b56
            , CONST 0x937459964dc03466
            , CONST 0xedd2ef2ca7949924
            , CONST 0xede9affde0e22f68
            , CONST 0x8515b9d6bac9282d
            , CONST 0x6b5c07b4e9e900d8
            , CONST 0x1ec66368838c8a08
            , CONST 0x9042367d80d1fbab
            , CONST 0x400283564a3c3799
            , CONST 0x4a00be0466bca75e ]
          , [ CONST 0x7913beee58e3817f
            , CONST 0xf545e88532237d90
            , CONST 0x22f8cb8736042005
            , CONST 0x6f04990e247a2623
            , CONST 0xfe22e87ba37c38cd
            , CONST 0xd20e32c85ffe2815
            , CONST 0x117227674048fe73
            , CONST 0x4e9fb7ea98a6b145
            , CONST 0xe0866c232b8af08b
            , CONST 0x00bbc77916884964
            , CONST 0x7031c0fb990d7116
            , CONST 0x240a9e87cf35108f ]
          , [ CONST 0x2e6363a5a12244b3
            , CONST 0x5e1c3787d1b5011c
            , CONST 0x4132660e2a196e8b
            , CONST 0x3a013b648d3d4327
            , CONST 0xf79839f49888ea43
            , CONST 0xfe85658ebafe1439
            , CONST 0xb6889825a14240bd
            , CONST 0x578453605541382b
            , CONST 0x4508cda8f6b63ce9
            , CONST 0x9c3ef35848684c91
            , CONST 0x0812bde23c87178c
            , CONST 0xfe49638f7f722c14 ]
          , [ CONST 0x8e3f688ce885cbf5
            , CONST 0xb8e110acf746a87d
            , CONST 0xb4b2e8973a6dabef
            , CONST 0x9e714c5da3d462ec
            , CONST 0x6438f9033d3d0c15
            , CONST 0x24312f7cf1a27199
            , CONST 0x23f843bb47acbf71
            , CONST 0x9183f11a34be9f01
            , CONST 0x839062fbb9d45dbf
            , CONST 0x24b56e7e6c2e43fa
            , CONST 0xe1683da61c962a72
            , CONST 0xa95c63971a19bfa7 ] ]

{-@ rc12_p :: [FieldDSL F_G] @-}
rc12_p :: [DSL F_G]
rc12_p = [ CONST 0x4adf842aa75d4316
         , CONST 0xf8fbb871aa4ab4eb
         , CONST 0x68e85b6eb2dd6aeb
         , CONST 0x07a0b06b2d270380
         , CONST 0xd94e0228bd282de4
         , CONST 0x8bdd91d3250c5278
         , CONST 0x209c68b88bba778f
         , CONST 0xb5e18cdab77f3877
         , CONST 0xb296a3e808da93fa
         , CONST 0x8370ecbda11a327e
         , CONST 0x3f9075283775dad8
         , CONST 0xb78095bb23c6aa84
         , CONST 0x3f36b9fe72ad4e5f
         , CONST 0x69bc96780b10b553
         , CONST 0x3f1d341f2eb7b881
         , CONST 0x4e939e9815838818
         , CONST 0xda366b3ae2a31604
         , CONST 0xbc89db1e7287d509
         , CONST 0x6102f411f9ef5659
         , CONST 0x58725c5e7ac1f0ab
         , CONST 0x0df5856c798883e7
         , CONST 0xf7bb62a8da4c961b ]

{-@ rc12_f2 :: [VecDSL' F_G 12] @-}
rc12_f2 :: [DSL F_G]
rc12_f2 = map (fromList TF)
          [ [ CONST 0xc68be7c94882a24d
            , CONST 0xaf996d5d5cdaedd9
            , CONST 0x9717f025e7daf6a5
            , CONST 0x6436679e6e7216f4
            , CONST 0x8a223d99047af267
            , CONST 0xbb512e35a133ba9a
            , CONST 0xfbbf44097671aa03
            , CONST 0xf04058ebf6811e61
            , CONST 0x5cca84703fac7ffb
            , CONST 0x9b55c7945de6469f
            , CONST 0x8e05bf09808e934f
            , CONST 0x2ea900de876307d7 ]
          , [ CONST 0x7748fff2b38dfb89
            , CONST 0x6b99a676dd3b5d81
            , CONST 0xac4bb7c627cf7c13
            , CONST 0xadb6ebe5e9e2f5ba
            , CONST 0x2d33378cafa24ae3
            , CONST 0x1e5b73807543f8c2
            , CONST 0x09208814bfebb10f
            , CONST 0x782e64b6bb5b93dd
            , CONST 0xadd5a48eac90b50f
            , CONST 0xadd4c54c736ea4b1
            , CONST 0xd58dbb86ed817fd8
            , CONST 0x6d5ed1a533f34ddd ]
          , [ CONST 0x28686aa3e36b7cb9
            , CONST 0x591abd3476689f36
            , CONST 0x047d766678f13875
            , CONST 0xa2a11112625f5b49
            , CONST 0x21fd10a3f8304958
            , CONST 0xf9b40711443b0280
            , CONST 0xd2697eb8b2bde88e
            , CONST 0x3493790b51731b3f
            , CONST 0x11caf9dd73764023
            , CONST 0x7acfb8f72878164e
            , CONST 0x744ec4db23cefc26
            , CONST 0x1e00e58f422c6340 ]
          , [ CONST 0x21dd28d906a62dda
            , CONST 0xf32a46ab5f465b5f
            , CONST 0xbfce13201f3f7e6b
            , CONST 0xf30d2e7adb5304e2
            , CONST 0xecdf4ee4abad48e9
            , CONST 0xf94e82182d395019
            , CONST 0x4ee52e3744d887c5
            , CONST 0xa1341c7cac0083b2
            , CONST 0x2302fb26c30c834a
            , CONST 0xaea3c587273bf7d3
            , CONST 0xf798e24961823ec7
            , CONST 0x962deba3e9a2cd94 ] ]

{-@ reflect goldilocks_12 @-}
goldilocks_12 :: Instance F_G
goldilocks_12 = Ins 12 7 matDiag12_M1 rc12_f1 rc12_p rc12_f2

-- t = 16 ----------------------------------------------------------------------

{-@ matDiag16_M1 :: VecDSL' F_G 16 @-}
matDiag16_M1 :: DSL F_G
matDiag16_M1 = fromList TF
               [ CONST 0xde9b91a467d6afc0
               , CONST 0xc5f16b9c76a9be17
               , CONST 0x0ab0fef2d540ac55
               , CONST 0x3001d27009d05773
               , CONST 0xed23b1f906d3d9eb
               , CONST 0x5ce73743cba97054
               , CONST 0x1c3bab944af4ba24
               , CONST 0x2faa105854dbafae
               , CONST 0x53ffb3ae6d421a10
               , CONST 0xbcda9df8884ba396
               , CONST 0xfc1273e4a31807bb
               , CONST 0xc77952573d5142c0
               , CONST 0x56683339a819b85e
               , CONST 0x328fcbd8f0ddc8eb
               , CONST 0xb5101e303fce9cb7
               , CONST 0x774487b8c40089bb ]

{-@ rc16_f1 :: [VecDSL' F_G 16] @-}
rc16_f1 :: [DSL F_G]
rc16_f1 = map (fromList TF)
          [ [ CONST 0x15ebea3fc73397c3
            , CONST 0xd73cd9fbfe8e275c
            , CONST 0x8c096bfce77f6c26
            , CONST 0x4e128f68b53d8fea
            , CONST 0x29b779a36b2763f6
            , CONST 0xfe2adc6fb65acd08
            , CONST 0x8d2520e725ad0955
            , CONST 0x1c2392b214624d2a
            , CONST 0x37482118206dcc6e
            , CONST 0x2f829bed19be019a
            , CONST 0x2fe298cb6f8159b0
            , CONST 0x2bbad982deccdbbf
            , CONST 0xbad568b8cc60a81e
            , CONST 0xb86a814265baad10
            , CONST 0xbec2005513b3acb3
            , CONST 0x6bf89b59a07c2a94 ]
          , [ CONST 0xa25deeb835e230f5
            , CONST 0x3c5bad8512b8b12a
            , CONST 0x7230f73c3cb7a4f2
            , CONST 0xa70c87f095c74d0f
            , CONST 0x6b7606b830bb2e80
            , CONST 0x6cd467cfc4f24274
            , CONST 0xfeed794df42a9b0a
            , CONST 0x8cf7cf6163b7dbd3
            , CONST 0x9a6e9dda597175a0
            , CONST 0xaa52295a684faf7b
            , CONST 0x017b811cc3589d8d
            , CONST 0x55bfb699b6181648
            , CONST 0xc2ccaf71501c2421
            , CONST 0x1707950327596402
            , CONST 0xdd2fcdcd42a8229f
            , CONST 0x8b9d7d5b27778a21 ]
          , [ CONST 0xac9a05525f9cf512
            , CONST 0x2ba125c58627b5e8
            , CONST 0xc74e91250a8147a5
            , CONST 0xa3e64b640d5bb384
            , CONST 0xf53047d18d1f9292
            , CONST 0xbaaeddacae3a6374
            , CONST 0xf2d0914a808b3db1
            , CONST 0x18af1a3742bfa3b0
            , CONST 0x9a621ef50c55bdb8
            , CONST 0xc615f4d1cc5466f3
            , CONST 0xb7fbac19a35cf793
            , CONST 0xd2b1a15ba517e46d
            , CONST 0x4a290c4d7fd26f6f
            , CONST 0x4f0cf1bb1770c4c4
            , CONST 0x548345386cd377f5
            , CONST 0x33978d2789fddd42 ]
          , [ CONST 0xab78c59deb77e211
            , CONST 0xc485b2a933d2be7f
            , CONST 0xbde3792c00c03c53
            , CONST 0xab4cefe8f893d247
            , CONST 0xc5c0e752eab7f85f
            , CONST 0xdbf5a76f893bafea
            , CONST 0xa91f6003e3d984de
            , CONST 0x099539077f311e87
            , CONST 0x097ec52232f9559e
            , CONST 0x53641bdf8991e48c
            , CONST 0x2afe9711d5ed9d7c
            , CONST 0xa7b13d3661b5d117
            , CONST 0x5a0e243fe7af6556
            , CONST 0x1076fae8932d5f00
            , CONST 0x9b53a83d434934e3
            , CONST 0xed3fd595a3c0344a ] ]

{-@ rc16_p :: [FieldDSL F_G] @-}
rc16_p :: [DSL F_G]
rc16_p = [ CONST 0x28eff4b01103d100
         , CONST 0x60400ca3e2685a45
         , CONST 0x1c8636beb3389b84
         , CONST 0xac1332b60e13eff0
         , CONST 0x2adafcc364e20f87
         , CONST 0x79ffc2b14054ea0b
         , CONST 0x3f98e4c0908f0a05
         , CONST 0xcdb230bc4e8a06c4
         , CONST 0x1bcaf7705b152a74
         , CONST 0xd9bca249a82a7470
         , CONST 0x91e24af19bf82551
         , CONST 0xa62b43ba5cb78858
         , CONST 0xb4898117472e797f
         , CONST 0xb3228bca606cdaa0
         , CONST 0x844461051bca39c9
         , CONST 0xf3411581f6617d68
         , CONST 0xf7fd50646782b533
         , CONST 0x6ca664253c18fb48
         , CONST 0x2d2fcdec0886a08f
         , CONST 0x29da00dd799b575e
         , CONST 0x47d966cc3b6e1e93
         , CONST 0xde884e9a17ced59e ]

{-@ rc16_f2 :: [VecDSL' F_G 16] @-}
rc16_f2 :: [DSL F_G]
rc16_f2 = map (fromList TF)
          [ [ CONST 0xdacf46dc1c31a045
            , CONST 0x5d2e3c121eb387f2
            , CONST 0x51f8b0658b124499
            , CONST 0x1e7dbd1daa72167d
            , CONST 0x8275015a25c55b88
            , CONST 0xe8521c24ac7a70b3
            , CONST 0x6521d121c40b3f67
            , CONST 0xac12de797de135b0
            , CONST 0xafa28ead79f6ed6a
            , CONST 0x685174a7a8d26f0b
            , CONST 0xeff92a08d35d9874
            , CONST 0x3058734b76dd123a
            , CONST 0xfa55dcfba429f79c
            , CONST 0x559294d4324c7728
            , CONST 0x7a770f53012dc178
            , CONST 0xedd8f7c408f3883b ]
          , [ CONST 0x39b533cf8d795fa5
            , CONST 0x160ef9de243a8c0a
            , CONST 0x431d52da6215fe3f
            , CONST 0x54c51a2a2ef6d528
            , CONST 0x9b13892b46ff9d16
            , CONST 0x263c46fcee210289
            , CONST 0xb738c96d25aabdc4
            , CONST 0x5c33a5203996d38f
            , CONST 0x2626496e7c98d8dd
            , CONST 0xc669e0a52785903a
            , CONST 0xaecde726c8ae1f47
            , CONST 0x039343ef3a81e999
            , CONST 0x2615ceaf044a54f9
            , CONST 0x7e41e834662b66e1
            , CONST 0x4ca5fd4895335783
            , CONST 0x64b334d02916f2b0 ]
          , [ CONST 0x87268837389a6981
            , CONST 0x034b75bcb20a6274
            , CONST 0x58e658296cc2cd6e
            , CONST 0xe2d0f759acc31df4
            , CONST 0x81a652e435093e20
            , CONST 0x0b72b6e0172eaf47
            , CONST 0x4aec43cec577d66d
            , CONST 0xde78365b028a84e6
            , CONST 0x444e19569adc0ee4
            , CONST 0x942b2451fa40d1da
            , CONST 0xe24506623ea5bd6c
            , CONST 0x082854bf2ef7c743
            , CONST 0x69dbbc566f59d62e
            , CONST 0x248c38d02a7b5cb2
            , CONST 0x4f4e8f8c09d15edb
            , CONST 0xd96682f188d310cf ]
          , [ CONST 0x6f9a25d56818b54c
            , CONST 0xb6cefed606546cd9
            , CONST 0x5bc07523da38a67b
            , CONST 0x7df5a3c35b8111cf
            , CONST 0xaaa2cc5d4db34bb0
            , CONST 0x9e673ff22a4653f8
            , CONST 0xbd8b278d60739c62
            , CONST 0xe10d20f6925b8815
            , CONST 0xf6c87b91dd4da2bf
            , CONST 0xfed623e2f71b6f1a
            , CONST 0xa0f02fa52a94d0d3
            , CONST 0xbb5794711b39fa16
            , CONST 0xd3b94fba9d005c7f
            , CONST 0x15a26e89fad946c9
            , CONST 0xf3cb87db8a67cf49
            , CONST 0x400d2bf56aa2a577 ] ]

{-@ reflect goldilocks_16 @-}
goldilocks_16 :: Instance F_G
goldilocks_16 = Ins 16 7 matDiag16_M1 rc16_f1 rc16_p rc16_f2

-- t = 20 ----------------------------------------------------------------------

{-@ matDiag20_M1 :: VecDSL' F_G 20 @-}
matDiag20_M1 :: DSL F_G
matDiag20_M1 = fromList TF
               [ CONST 0x95c381fda3b1fa57
               , CONST 0xf36fe9eb1288f42c
               , CONST 0x89f5dcdfef277944
               , CONST 0x106f22eadeb3e2d2
               , CONST 0x684e31a2530e5111
               , CONST 0x27435c5d89fd148e
               , CONST 0x3ebed31c414dbf17
               , CONST 0xfd45b0b2d294e3cc
               , CONST 0x48c904473a7f6dbf
               , CONST 0xe0d1b67809295b4d
               , CONST 0xddd1941e9d199dcb
               , CONST 0x8cfe534eeb742219
               , CONST 0xa6e5261d9e3b8524
               , CONST 0x6897ee5ed0f82c1b
               , CONST 0x0e7dcd0739ee5f78
               , CONST 0x493253f3d0d32363
               , CONST 0xbb2737f5845f05c0
               , CONST 0xa187e810b06ad903
               , CONST 0xb635b995936c4918
               , CONST 0x0b3694a940bd2394 ]

{-@ rc20_f1 :: [VecDSL' F_G 20] @-}
rc20_f1 :: [DSL F_G]
rc20_f1 = map (fromList TF)
          [ [ CONST 0xf50674557d527f42
            , CONST 0x8b33e51b9306c9fb
            , CONST 0x04cfcb30bb344eb3
            , CONST 0x5ea8bec44640c87d
            , CONST 0xd84af685a9708e36
            , CONST 0x5b33851fa07aeba4
            , CONST 0xeb7cbc374f3b5ca1
            , CONST 0xecaaea4a76acdd63
            , CONST 0x2b1fa14802fdf5ba
            , CONST 0xabd29defd98c932a
            , CONST 0x280febc703c6f6bc
            , CONST 0x8421653ddb551263
            , CONST 0xd75332a308377a9a
            , CONST 0xe45ce859b4936b93
            , CONST 0xe78d6432dae2a36a
            , CONST 0x577b3e8e105daa7c
            , CONST 0x81b584e5beba6b37
            , CONST 0x0f68acc5174b4131
            , CONST 0x9778789f2bdcf224
            , CONST 0x2168764b99769f7b ]
          , [ CONST 0x5a413448ea188080
            , CONST 0x477f5ced7153ebcb
            , CONST 0x5fd53ff5d03a419a
            , CONST 0x1a2c5db9b1d8920f
            , CONST 0xf72f9208355e32b9
            , CONST 0x48b703a56669bb32
            , CONST 0x7cc279c1c07bc372
            , CONST 0xd27e3611c012ce04
            , CONST 0xf16771e825f6e903
            , CONST 0x78e2f60a6f3be068
            , CONST 0x58e163e91557e816
            , CONST 0x5b73573f7a257c27
            , CONST 0x0061099de80b8dec
            , CONST 0x455a75647c9d9667
            , CONST 0x7098d056e4cf6d14
            , CONST 0x31678c815e7b8e0b
            , CONST 0xe492d70c4a3b9961
            , CONST 0x3229a663cdb553c1
            , CONST 0x991dbb8e6bb94f68
            , CONST 0xae0c1a23ab319d98 ]
          , [ CONST 0x68caee423f6c1ca8
            , CONST 0x88d5d56d052133ad
            , CONST 0x944cb4e601ab885b
            , CONST 0xad0ad397c02cb6b6
            , CONST 0x48eb1c25917f47ab
            , CONST 0x0b586ca072e551a5
            , CONST 0x7620eec7fdf7caf2
            , CONST 0xdc01964b2c304322
            , CONST 0xdfce38c4e7eeb165
            , CONST 0xc295f9569e1bb057
            , CONST 0xfaa09073be956353
            , CONST 0x2bcd086ac04a51a8
            , CONST 0xcebaf7d11c46f141
            , CONST 0x2d8c6f303321f3db
            , CONST 0xc6866bec13a24a73
            , CONST 0xf94822529997b647
            , CONST 0x2e7c7fb5dadf4875
            , CONST 0x7f217e80452ad2fd
            , CONST 0x960769bf3f80475b
            , CONST 0x6e474087b9c8ef41 ]
          , [ CONST 0x7a3c61782d3cdb1e
            , CONST 0x34f6202a97d34913
            , CONST 0x384eb863f122f34f
            , CONST 0x0dd0a16eeef9f245
            , CONST 0xc7b7a83c63c05ca0
            , CONST 0x5a9c01c5b1711fb3
            , CONST 0x622bd3594411269e
            , CONST 0x1411eedfa8800f63
            , CONST 0x63264ba3307daa57
            , CONST 0x650fcf71ce431a7c
            , CONST 0xb391425703d4db0b
            , CONST 0x2527ee4c34183aaa
            , CONST 0xbb8d239eb87d1b85
            , CONST 0x1fee0fb1866e793d
            , CONST 0xda1a1b59ed24ecbd
            , CONST 0xde4e502b21d3a750
            , CONST 0x0ecfcc5d86a85661
            , CONST 0xc6743030d6cdfff0
            , CONST 0x1fdd06ecbc98c107
            , CONST 0xdf68661118e969b4 ] ]

{-@ rc20_p :: [FieldDSL F_G] @-}
rc20_p :: [DSL F_G]
rc20_p = [ CONST 0xb4c4646b481ab94b
         , CONST 0x3a6dd8f34a4b672d
         , CONST 0xe4a13a0271f8c398
         , CONST 0xb8c4d81a0f3f87c6
         , CONST 0x3bb4717250f0add9
         , CONST 0x27ad39cf9b261444
         , CONST 0x153a3fc8b666d830
         , CONST 0x958023df70e2f9ba
         , CONST 0xe5a98af0507e5112
         , CONST 0xff4c17fffffd4ccb
         , CONST 0x3f033e0e60932043
         , CONST 0x79995f1fd8b0ed93
         , CONST 0x5fccc385058f90de
         , CONST 0x121495895f0337f2
         , CONST 0xea4329ff4a44fc89
         , CONST 0x9e582ef77f57587a
         , CONST 0xdd355989ec73626b
         , CONST 0xe1542c0dcd6602ad
         , CONST 0x9ce00cbfa5c788b7
         , CONST 0x5b5e142bd67da0e9
         , CONST 0xddae0051d202fd78
         , CONST 0xe8d5708621548b09 ]

{-@ rc20_f2 :: [VecDSL' F_G 20] @-}
rc20_f2 :: [DSL F_G]
rc20_f2 = map (fromList TF)
          [ [ CONST 0x546948156f481f23
            , CONST 0xb969557898da1c1f
            , CONST 0xeb2fb3be05e81624
            , CONST 0x5fd250a0ded7ddfc
            , CONST 0x7abd52aa764e2a35
            , CONST 0xc8d101b1c0a4595e
            , CONST 0x300cb802ad939c00
            , CONST 0x16d4a6ac828e4842
            , CONST 0xd763f9f3377a0d88
            , CONST 0xb842c1778267fb5b
            , CONST 0x7998fca5e0508c18
            , CONST 0x08980b89d5d95b1e
            , CONST 0x5fc3c05cb8b2a5b7
            , CONST 0xe8263579c08b15ed
            , CONST 0x1c85bc5bdee01834
            , CONST 0x496efa05ae9f7e59
            , CONST 0x26cdfc330f0c6d44
            , CONST 0x2da38a687f2efd4e
            , CONST 0x242721a16c92bd03
            , CONST 0xd150bae390c7f3de ]
          , [ CONST 0xa17440c7563bda85
            , CONST 0x1b52c08ccc72cffc
            , CONST 0x0853bbd066be2f8c
            , CONST 0xb140631d97249d92
            , CONST 0x31ed98f8f4e8bc2a
            , CONST 0xb7b4c6534fa6ad28
            , CONST 0xc31ae7f908b28f94
            , CONST 0xf2e7d14d33db910d
            , CONST 0x408cd1daa30e5d85
            , CONST 0x67635e708b67e913
            , CONST 0x0f41e00c44bbcddd
            , CONST 0x306ec73b35427165
            , CONST 0xb19cc1e7013a0c83
            , CONST 0x598948784a1d8dfb
            , CONST 0xcd0d07046113b3a4
            , CONST 0x9f5777a149e7100f
            , CONST 0x52e16bce7d6ce553
            , CONST 0x4dfd369bb3a4e49f
            , CONST 0x6721381077a7facf
            , CONST 0x84fae431fad2a352 ]
          , [ CONST 0xb57b0b6da95609a3
            , CONST 0x1f3487a56048fd5f
            , CONST 0x6de8f1ff46eb8de7
            , CONST 0x790ff3c21234db43
            , CONST 0x0fa75c59f4291147
            , CONST 0x41baef249921ddb6
            , CONST 0x8f3049fb127bec11
            , CONST 0x5d1239a25594fa4b
            , CONST 0x011956aca10824ee
            , CONST 0x25665f341261989b
            , CONST 0x7d12eaf643734d3c
            , CONST 0xeace4b846cd0a06b
            , CONST 0x6c7157cc1760a5ac
            , CONST 0xb0e83ddf39a63764
            , CONST 0xfab9e612681227fb
            , CONST 0x0cf7f0d62238655e
            , CONST 0xc32a0826ca5643bb
            , CONST 0x4fbd2e4d1bd8f2b0
            , CONST 0xc6c94a369f4ac8d5
            , CONST 0x8cf524c8b7774cb2 ]
          , [ CONST 0x8a8a7159ca118c8c
            , CONST 0x7020e0efee7c62ed
            , CONST 0xb82c8f0d0abaacf6
            , CONST 0xdb1b8170627bcabd
            , CONST 0x89f751dac47b2e6e
            , CONST 0xd5a68b7ad8b8ad75
            , CONST 0x01c2c6f90a9cb8a9
            , CONST 0x749f9c0919bff4f3
            , CONST 0x52713fb5d3f6e8d0
            , CONST 0x6c246db24bfafbd9
            , CONST 0x483e5244b3f8adf0
            , CONST 0x670755cdb87a4c39
            , CONST 0xa2bf8de7fd0b4d78
            , CONST 0x3334c74fce39902b
            , CONST 0x3885406d5ea81e21
            , CONST 0x8dfbd465694a0354
            , CONST 0xce8f5388e86080d9
            , CONST 0x89108c704fc3ced7
            , CONST 0xf4896b0b26d80f23
            , CONST 0xb4fd29f241f11176 ] ]

{-@ reflect goldilocks_20 @-}
goldilocks_20 :: Instance F_G
goldilocks_20 = Ins 20 7 matDiag20_M1 rc20_f1 rc20_p rc20_f2

-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
