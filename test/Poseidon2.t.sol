// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Field, Poseidon2, Poseidon2Lib} from "../src/Poseidon2.sol";
import {Poseidon2Yul} from "../src/Poseidon2Yul.sol";
import {HuffDeployer} from "foundry-huff/HuffDeployer.sol";

contract Poseidon2Test is Test {
    using Field for *;
    using Poseidon2Lib for *;

    Poseidon2 private poseidon2;
    address private poseidon2Yul;
    // address private poseidon2Huff;

    function setUp() public  {
        poseidon2 = new Poseidon2();
        poseidon2Yul = address(new Poseidon2Yul());
        // poseidon2Huff = HuffDeployer.deploy("Poseidon2");
    }

    function poseidon2Yul_1(uint256 a) internal view returns (uint256 decoded) {
        assembly {
            mstore(0, a)
            let res := staticcall(gas(), sload(poseidon2Yul.slot), 0, 0x20, 0, 0x20)
            decoded := mload(0)
        }
        return decoded;
    }

    function poseidon2Yul_2(uint256 a, uint256 b) internal view returns (uint256 decoded) {
        assembly {
            mstore(0, a)
            mstore(0x20, b)
            let res := staticcall(gas(), sload(poseidon2Yul.slot), 0, 0x40, 0, 0x20)
            decoded := mload(0)
        }
    }

    function poseidon2Yul_3(uint256 a, uint256 b, uint256 c) internal view returns (uint256 decoded) {
        bytes memory input = abi.encode(a, b, c);
        (, bytes memory result) = poseidon2Yul.staticcall(input);
        assembly {
            decoded := mload(add(result, 0x20))
        }
    }

    function test_hash_1_through_library() public view {
        Poseidon2Lib.Constants memory _poseidon = Poseidon2Lib.load();
        assertEq(
            _poseidon.hash_1(uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField())
                .toUint256(),
            0x2710144414c3a5f2354f4c08d52ed655b9fe253b4bf12cb9ad3de693d9b1db11
        );
    }

    function test_var_length_hash_through_library() public view {
        Poseidon2Lib.Constants memory _poseidon = Poseidon2Lib.load();

        Field.Type[] memory input = new Field.Type[](1); 
        assertEq(
            _poseidon.hash_internal(input, 2, true).toUint256(),
            0x57985cb452f268c650a6600d9410f49ebd2fd9756b8c89f38cf80a72e5a4f1a
        );
    }

    // Hashing one element

    function test_hash_1_a() public view {
        assertEq(
            poseidon2.hash_1(uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField())
                .toUint256(),
            0x2710144414c3a5f2354f4c08d52ed655b9fe253b4bf12cb9ad3de693d9b1db11
        );
    }

    function test_hash_1_b() public view {
        assertEq(
            poseidon2.hash_1(uint256(0x19f3d19e5dd8b29a42cea4f71ebc6b12a42a5edbafbcb89cf0cddf0995d44e7f).toField())
                .toUint256(),
            0x2e1874598412a3b19f824ff246a1949a38b365bcdd58807eedb9206288820232
        );
    }

    function test_hash_1_c() public view {
        assertEq(
            poseidon2.hash_1(uint256(0x0049c16ff91dacf0cb573751342f7bfa0042819e3f15fce57d61339f6340b0c1).toField())
                .toUint256(),
            0x011b5e5c76aedd3a361d2c72c711425f5709988da3c226bb8536691d81b190ac
        );
    }

    function test_hash_1_d() public view {
        assertEq(
            poseidon2.hash_1(uint256(0x02713077725e5498d596be781be4c9a7353dbfe70ff10dc17702e66d0b5d388c).toField())
                .toUint256(),
            0x2ee1f0fc41b250f0e26dbaa1e9dc0d8e27e9354baf3c11eca131994c119f5651
        );
    }

    function test_hash_1_e() public view {
        assertEq(
            poseidon2.hash_1(uint256(0x2a84a08a631f4c391b02f4519720881a80c25eb6ba3b59b2ca8f3c0e22ebeebc).toField())
                .toUint256(),
            0x0cf97e83eb7aa42f60e85095836d3b0afe3e88cc5046e1bae7318a64a0d32fd5
        );
    }

    // Hashing one element through Yul

    function test_hash_1_a_yul() public view {
        assertEq(poseidon2Yul_1(0), 0x2710144414c3a5f2354f4c08d52ed655b9fe253b4bf12cb9ad3de693d9b1db11);
    }

    function test_hash_1_b_yul() public view {
        assertEq(
            poseidon2Yul_1(0x19f3d19e5dd8b29a42cea4f71ebc6b12a42a5edbafbcb89cf0cddf0995d44e7f),
            0x2e1874598412a3b19f824ff246a1949a38b365bcdd58807eedb9206288820232
        );
    }

    function test_hash_1_c_yul() public view {
        assertEq(
            poseidon2Yul_1(0x0049c16ff91dacf0cb573751342f7bfa0042819e3f15fce57d61339f6340b0c1),
            0x011b5e5c76aedd3a361d2c72c711425f5709988da3c226bb8536691d81b190ac
        );
    }

    function test_hash_1_d_yul() public view {
        assertEq(
            poseidon2Yul_1(0x02713077725e5498d596be781be4c9a7353dbfe70ff10dc17702e66d0b5d388c),
            0x2ee1f0fc41b250f0e26dbaa1e9dc0d8e27e9354baf3c11eca131994c119f5651
        );
    }

    function test_hash_1_e_yul() public view {
        assertEq(
            poseidon2Yul_1(0x2a84a08a631f4c391b02f4519720881a80c25eb6ba3b59b2ca8f3c0e22ebeebc),
            0x0cf97e83eb7aa42f60e85095836d3b0afe3e88cc5046e1bae7318a64a0d32fd5
        );
    }

    // Hashing two elements

    function test_hash_2_a() public view {
        assertEq(
            poseidon2.hash_2(
                uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField(),
                uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField()
            ).toUint256(),
            0x0b63a53787021a4a962a452c2921b3663aff1ffd8d5510540f8e659e782956f1
        );
    }

    function test_hash_2_b() public view {
        assertEq(
            poseidon2.hash_2(
                uint256(0x1762d324c2db6a912e607fd09664aaa02dfe45b90711c0dae9627d62a4207788).toField(),
                uint256(0x1047bd52da536f6bdd26dfe642d25d9092c458e64a78211298648e81414cbf35).toField()
            ).toUint256(),
            0x303cacb84a267e5f3f46914fd3262dcaa212930c27a2f9de22c080dd9857be35
        );
    }

    function test_hash_2_c() public view {
        assertEq(
            poseidon2.hash_2(
                uint256(0x0a529bb6bbbf25ed33a47a4637dc70eb469a29893047482866748ae7f3a5afe1).toField(),
                uint256(0x1f5189751e18cf788deb219bdb95461e86ca08a882e4af5f8a6ec478e1ec73b4).toField()
            ).toUint256(),
            0x1f71000626ba87581561f94a17f7b9962be8f1aa8d0c69c6f95348c9ddffe542
        );
    }

    function test_hash_2_d() public view {
        assertEq(
            poseidon2.hash_2(
                uint256(0x14ba77172ab2278bdf5a087ca0bd400e936bafe6dfc092c4e7a1b0950f1b6dbe).toField(),
                uint256(0x195c41f12d4fbac5e194c201536f3094541e73bf27d9f2413f09e731b3838733).toField()
            ).toUint256(),
            0x06b53c119381e6ccee8e3ac9845970ba96befbce39606fad3686a6e31ac7761e
        );
    }

    function test_hash_2_e() public view {
        assertEq(
            poseidon2.hash_2(
                uint256(0x2079041f0d6becd26db3ec659c54f60464243d86c3982978f1217a5f1413ed3a).toField(),
                uint256(0x08146641a4e30689442ecd270a7efef725bdb3036bf3d837dff683161a455de1).toField()
            ).toUint256(),
            0x07512888968a4cfc7e5da7537c7f4448bf04d3679e711c3f16ca86351b0d1e6b
        );
    }

    // Hashing two elements through Yul

    function test_hash_2_a_yul() public view {
        assertEq(poseidon2Yul_2(0, 0), 0x0b63a53787021a4a962a452c2921b3663aff1ffd8d5510540f8e659e782956f1);
    }

    function test_hash_2_b_yul() public view {
        assertEq(
            poseidon2Yul_2(
                0x1762d324c2db6a912e607fd09664aaa02dfe45b90711c0dae9627d62a4207788,
                0x1047bd52da536f6bdd26dfe642d25d9092c458e64a78211298648e81414cbf35
            ),
            0x303cacb84a267e5f3f46914fd3262dcaa212930c27a2f9de22c080dd9857be35
        );
    }

    function test_hash_2_c_yul() public view {
        assertEq(
            poseidon2Yul_2(
                0x0a529bb6bbbf25ed33a47a4637dc70eb469a29893047482866748ae7f3a5afe1,
                0x1f5189751e18cf788deb219bdb95461e86ca08a882e4af5f8a6ec478e1ec73b4
            ),
            0x1f71000626ba87581561f94a17f7b9962be8f1aa8d0c69c6f95348c9ddffe542
        );
    }

    function test_hash_2_d_yul() public view {
        assertEq(
            poseidon2Yul_2(
                0x14ba77172ab2278bdf5a087ca0bd400e936bafe6dfc092c4e7a1b0950f1b6dbe,
                0x195c41f12d4fbac5e194c201536f3094541e73bf27d9f2413f09e731b3838733
            ),
            0x06b53c119381e6ccee8e3ac9845970ba96befbce39606fad3686a6e31ac7761e
        );
    }

    function test_hash_2_e_yul() public view {
        assertEq(
            poseidon2Yul_2(
                0x2079041f0d6becd26db3ec659c54f60464243d86c3982978f1217a5f1413ed3a,
                0x08146641a4e30689442ecd270a7efef725bdb3036bf3d837dff683161a455de1
            ),
            0x07512888968a4cfc7e5da7537c7f4448bf04d3679e711c3f16ca86351b0d1e6b
        );
    }

    // Hashing three elements

    function test_hash_3_a() public view {
        assertEq(
            poseidon2.hash_3(
                uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField(),
                uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField(),
                uint256(0x0000000000000000000000000000000000000000000000000000000000000000).toField()
            ).toUint256(),
            0x2a5de47ed300af27b706aaa14762fc468f5cfc16cd8116eb6b09b0f2643ca2b9
        );
    }

    function test_hash_3_b() public view {
        assertEq(
            poseidon2.hash_3(
                uint256(0x300ced31bf248a1a2d4ea02b5e9f302a9e34df3c2109d5f1046ee9f59de6f6f1).toField(),
                uint256(0x2e6eb409ed7f41949cdb1925ac3ec68132b2443d873589a8afde4c027c3c0b68).toField(),
                uint256(0x2f08443953fc54fb351e41a46da99bbec1d290dae2907d2baf5174ed28eee9ea).toField()
            ).toUint256(),
            0x27e4cf07e4bf24219f6a2da9be19cea601313a95f8a1360cf8f15d474826bf49
        );
    }

    function test_hash_3_c() public view {
        assertEq(
            poseidon2.hash_3(
                uint256(0x21c6e3a949ec9c622e7e062efab3d6e1d5ee62763f99366627de157e26d179b7).toField(),
                uint256(0x1369519755b97bf50d10be283f853c5607ed1308f8235cd34c915783cbf7c70d).toField(),
                uint256(0x00c632d6fe8be14eddb11aee10b63e017e7d1f1a275d01e9d215f4135e950e7d).toField()
            ).toUint256(),
            0x0d72d2b806a47af41117f7de2147908eb0496f99c0f58fbd6f5e778174132451
        );
    }

    function test_hash_3_d() public view {
        assertEq(
            poseidon2.hash_3(
                uint256(0x26001a9f75eddc947cfc2e7a5524a7fb32d226404468168d58ff2f918e027015).toField(),
                uint256(0x0080918fd6c6f3867a46a0260e2cc2bc6b0b6bcb4528d33ba2bb57555a12929a).toField(),
                uint256(0x05217f0ada44bebd06d9fd34358fe7213446bdce940d943916acb59cabdc0001).toField()
            ).toUint256(),
            0x2015f0a35636e589ae36e65f00b8f8c8a0cab01dcd080c23c8e2274283a57c85
        );
    }

    function test_hash_3_e() public view {
        assertEq(
            poseidon2.hash_3(
                uint256(0x2a7efeb117f6894cfa21375d4496249c43eda35b5d5d267b7154413fdaad44ea).toField(),
                uint256(0x0bb48b46f770205618e2350c2f9c294524425763fb7ef6156c33c5bc2b8c1cbf).toField(),
                uint256(0x0206c176b0c66212fd12a580a8dd38689ae29dfa15933ba1982f5d30ed0c2ea1).toField()
            ).toUint256(),
            0x1c93b16c25fa1e7b4933425b32876fa97c2013d44214792231634d3c96b6cc3f
        );
    }

    // Hashing three elements through Yul

    function test_hash_3_a_yul() public view {
        assertEq(poseidon2Yul_3(0, 0, 0), 0x2a5de47ed300af27b706aaa14762fc468f5cfc16cd8116eb6b09b0f2643ca2b9);
    }

    function test_hash_3_b_yul() public view {
        assertEq(
            poseidon2Yul_3(
                0x300ced31bf248a1a2d4ea02b5e9f302a9e34df3c2109d5f1046ee9f59de6f6f1,
                0x2e6eb409ed7f41949cdb1925ac3ec68132b2443d873589a8afde4c027c3c0b68,
                0x2f08443953fc54fb351e41a46da99bbec1d290dae2907d2baf5174ed28eee9ea
            ),
            0x27e4cf07e4bf24219f6a2da9be19cea601313a95f8a1360cf8f15d474826bf49
        );
    }

    function test_hash_3_c_yul() public view {
        assertEq(
            poseidon2Yul_3(
                0x21c6e3a949ec9c622e7e062efab3d6e1d5ee62763f99366627de157e26d179b7,
                0x1369519755b97bf50d10be283f853c5607ed1308f8235cd34c915783cbf7c70d,
                0x00c632d6fe8be14eddb11aee10b63e017e7d1f1a275d01e9d215f4135e950e7d
            ),
            0x0d72d2b806a47af41117f7de2147908eb0496f99c0f58fbd6f5e778174132451
        );
    }

    function test_hash_3_d_yul() public view {
        assertEq(
            poseidon2Yul_3(
                0x26001a9f75eddc947cfc2e7a5524a7fb32d226404468168d58ff2f918e027015,
                0x0080918fd6c6f3867a46a0260e2cc2bc6b0b6bcb4528d33ba2bb57555a12929a,
                0x05217f0ada44bebd06d9fd34358fe7213446bdce940d943916acb59cabdc0001
            ),
            0x2015f0a35636e589ae36e65f00b8f8c8a0cab01dcd080c23c8e2274283a57c85
        );
    }

    function test_hash_3_e_yul() public view {
        assertEq(
            poseidon2Yul_3(
                0x2a7efeb117f6894cfa21375d4496249c43eda35b5d5d267b7154413fdaad44ea,
                0x0bb48b46f770205618e2350c2f9c294524425763fb7ef6156c33c5bc2b8c1cbf,
                0x0206c176b0c66212fd12a580a8dd38689ae29dfa15933ba1982f5d30ed0c2ea1
            ),
            0x1c93b16c25fa1e7b4933425b32876fa97c2013d44214792231634d3c96b6cc3f
        );
    }

    // Variable length hashing

    function test_hash_var_len_1() public view {
        Field.Type[] memory input = new Field.Type[](1);
        input[0] = uint256(0x187b4757bbf034ce7daaf3fdf2b735544d88da2033dea124500ff79484bce862).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x0961b57effa18e2dcbf5671e9400d10bc9214fbf39b149cfd8949731f61d2bfa);
    }

    function test_hash_var_len_2() public view {
        Field.Type[] memory input = new Field.Type[](2);
        input[0] = uint256(0x0143bc5d854ca7c33c27ad96dfe2c2443dd272a30a99f90f8f892ac7bbb4370e).toField();
        input[1] = uint256(0x2eb3d5587861dac05dfed4b7099dbdef57fc644504f297afb890c2df0c7212e7).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x0d34db78174c82c6a7d60cbf21f0fce80ef4ddc67e65881d6daca4e5ad8cd52d);
    }

    function test_hash_var_len_3() public view {
        Field.Type[] memory input = new Field.Type[](3);
        input[0] = uint256(0x030341179f0ef88190aa557f9b20bb4aa31f805f214e72741b5d3b3a2bccf5b6).toField();
        input[1] = uint256(0x00b88879f5765438ef691e40ad4a6223d421317c342888de56c7f8b995e27688).toField();
        input[2] = uint256(0x0727b4522492cfbe1b5be97a17ed5672487fd1dc2ad3d09bd033c55d1ba40c70).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x22024dabdd6a9dfb47eb26f9569fd048968a0db30c60f3f38d8b61274458437e);
    }

    function test_hash_var_len_4() public view {
        Field.Type[] memory input = new Field.Type[](4);
        input[0] = uint256(0x0891e9efa2b82224dccfee5171614168f84c4c99443c7e6e2753433a978f5955).toField();
        input[1] = uint256(0x01c81114d1f4eb857dfe3a8479760fd0c8e33d9ed6f42f8ee3eef974b85ef937).toField();
        input[2] = uint256(0x03a2238b91de1214a385af17ade25f2e71b6364b4d54dfb6e7ec96fd12be5a65).toField();
        input[3] = uint256(0x24cc93df58f07c156dd648edac3318420325db58ff1cccbc3d9a3cdb529f8469).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x24f3009e0089df4ae82f5dcde988fd9738ede4a6f51788c11c69b3e43a01b42b);
    }

    function test_hash_var_len_5() public view {
        Field.Type[] memory input = new Field.Type[](5);
        input[0] = uint256(0x283318d1c946e5a788c59267712f20383a610189d89d39c161d53e2ae22b9bb5).toField();
        input[1] = uint256(0x2f51c6b6cc030846b73d449e6f8f9cbe609038bc4ccdb4268dc486e1a0d9694f).toField();
        input[2] = uint256(0x04c4fb583a2d9d9ceb1927de6d251e09fa01950313d6640863de039a37bd376a).toField();
        input[3] = uint256(0x18f1ec5070a8f50dbb71bf03d130fccc420161b8ee5e6c6ffdb676c7a7d33189).toField();
        input[4] = uint256(0x11e539f3dd6bb505dde162c84f22eee58f2a95a62027f230442b26c8dc3f96fc).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x1cbfcd7746c46fcfa7ae67d32e0cafb6ac348ebcb6f5a5e8c579ec6daa96362b);
    }

    function test_hash_var_len_6() public view {
        Field.Type[] memory input = new Field.Type[](6);
        input[0] = uint256(0x01c93b681eb77d4d6af59d8f753d49d3a8839208f44471e68d67e52758cc923d).toField();
        input[1] = uint256(0x2a8f0abbca50b48935358452633b55e694d4d03357d7d5bdfddf08a117ada3b9).toField();
        input[2] = uint256(0x0c1a9c0b4e4a5315f111c078e411360bf54af39bfe2ffa2ce094aa6d57aa3343).toField();
        input[3] = uint256(0x12e80d94354e709fdc78c0d646a3763dd4dbeada2c7b27553f23cc6c32823e82).toField();
        input[4] = uint256(0x065929de60742283ec95df48428ca27e72bc8d4d114f172aff17c237b208d056).toField();
        input[5] = uint256(0x23ceb931dc1b76a8915466e0faedf56a5fe2169e650248663d9fecb75e5fa156).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x145023e2318ab81ba31e50cc62713441762c5132d5e6acbe6e88fd9f816473f1);
    }

    function test_hash_var_len_7() public view {
        Field.Type[] memory input = new Field.Type[](7);
        input[0] = uint256(0x213bba8cab8dac55a2a86deaabcd4303ad2b0762fd1d11950d54bc54aa056623).toField();
        input[1] = uint256(0x00872f0dd93bd2868b85a7822d07d31d18ccf92228c38167de7804319a019fa3).toField();
        input[2] = uint256(0x198ea672f81fd916f47ae9a5f24d6740c5e5e5c8a389166ce02d85731e71d8af).toField();
        input[3] = uint256(0x0f362421b36759e1364d4ba7e5894381f56009843afe307aee6cb28a58ab4702).toField();
        input[4] = uint256(0x28a750154b9935407757f85a9f2596ddf082ce5f74256fd8c1200fc04a5f6548).toField();
        input[5] = uint256(0x0044d022f6220947659be7ed057a37adebc8468fce1bc365b76b7664595dd31d).toField();
        input[6] = uint256(0x22a2c8eff174ea66dee3d53dda9d45d37b90b3c2d6820f233fb868f4b41fc83c).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x16f71f10bf199529eadbbf20b0aefd1aae7afdd756c385da64d4e74474b9623c);
    }

    function test_hash_var_len_8() public view {
        Field.Type[] memory input = new Field.Type[](8);
        input[0] = uint256(0x1d40c16d71a56182ae856c7f69412c62b29f1afd21376c9fe615c6bcd013723d).toField();
        input[1] = uint256(0x03281f89b9ac18f3a8199b7116453790560d43f2d1b70debb10379b6702b5e31).toField();
        input[2] = uint256(0x2391e7ffcf81c4fbe0bd44cd89ad173d6d1d9bf7c4325ca4b195f863b9fb9da9).toField();
        input[3] = uint256(0x0ecbc17f1a32f3163bc8bc704711aebedb0ad69d29f224fc8fb0851e7fc9c8c4).toField();
        input[4] = uint256(0x1ea5f8133edf27df211a66c7ba4304b9131cbde0b1832c2a182d9869a77c491b).toField();
        input[5] = uint256(0x224b14a1040873fd8f154e6d7b65db283ed2c422e5d14aa06ce3ed9d3cc69743).toField();
        input[6] = uint256(0x1bda12ff5af5e9a1b1f7dd8febb87e253ca0a4e43b16cd3b79818007f6f8d1bb).toField();
        input[7] = uint256(0x24a873345d569136d18164069fc60749aa57f8930ec8a52adde1f01967afbb7c).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x1b63be96f9b6bdeb09f103968aabac69252137ec863177a93a516e8120d662c4);
    }

    function test_hash_var_len_9() public view {
        Field.Type[] memory input = new Field.Type[](9);
        input[0] = uint256(0x04e673b5f868ff850c5db58bb9f32b60c564b09b57261fdcb45c32013379ec21).toField();
        input[1] = uint256(0x0ff51c3255f4bd470e3263e5295b757d091fc015b1348b0b30b8fcfa5cc9b818).toField();
        input[2] = uint256(0x08f7a1ec99bf817777942e1132ccd237980a01f1d3d9914bbaf4d8e74320a1ee).toField();
        input[3] = uint256(0x2f6deadbdaa28308134784b3615596492085de03f479f59e79044e5860c76b27).toField();
        input[4] = uint256(0x141a2f00b0cbc606fe887c806d46659a6dac8a0d15829e36f06e43eec13eb324).toField();
        input[5] = uint256(0x1a0eb99c6f3c44026e61a5e6e36c806a25db6cf674c5f0075210dfdd00122264).toField();
        input[6] = uint256(0x0be48f952b90e3dfad74a2b04ade94e7b02b677702bf32d94389ff1669fa9911).toField();
        input[7] = uint256(0x18de646adb3e2f5e2ac7cd21dbfbf9dbe91d97b9cfb5afc2e7735c6f292d4ffe).toField();
        input[8] = uint256(0x174bfedb2323aecff5c4952313b81d9b3fcda8ff71a4b762bd16bb9779afb731).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x2a33a41e1e3cca17e7b7a000ac5cfcb7f7783023c0563acb39ae5bfe2e0d3c8e);
    }

    function test_hash_var_len_10() public view {
        Field.Type[] memory input = new Field.Type[](10);
        input[0] = uint256(0x041035d2043ca613be600dc3643dff43a343548bfeb85f19ab2ff31dfec42fd1).toField();
        input[1] = uint256(0x0233cd5d2fff9f11b3675f38a7fd7f04efbfe9a95f114824c2e9c98e97a52d3e).toField();
        input[2] = uint256(0x2251141b94a8f419455457672f188b942079916217c2e1eefd7eceab022e8ba1).toField();
        input[3] = uint256(0x08d2cfe2bd8e054aa3488c2d8a6f7628503da3f4d450e30d4fea46a8700d4a26).toField();
        input[4] = uint256(0x1eb978a79a501b8df8c6312f3474e1f41d439492fdfed4240cbfef6b0a7b47a2).toField();
        input[5] = uint256(0x05e385c9b9093003379e7111b3d83846694b15a3072355bc1a6df3eeff6e95f4).toField();
        input[6] = uint256(0x0d91626c7f7e0ff655a973452f3eae713893f57ce2e078978e00ef0ffab48f67).toField();
        input[7] = uint256(0x0d51fcc8cdc21676e2d0d44d2caebcbedbd0c7f3149e7a2cb24f0f923c718f50).toField();
        input[8] = uint256(0x23cf8f1eda161dc7114e4774216a96a51430a4ed00bb94a9c22ffaf8158d9331).toField();
        input[9] = uint256(0x2060c8e16eaa344a1eb20bbc4179ad36c6c3d503716f329ce268677ecb76172f).toField();

        assertEq(poseidon2.hash(input).toUint256(), 0x1eab26c4915afff7148c904edac0220dc6b86dca67ee342db5705027c4e489f1);
    }
}
