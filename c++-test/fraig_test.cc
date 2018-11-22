
/// @file equiv_test.cc
/// @brief equiv_test の実装ファイル
/// @author Yusuke Matsunaga (松永 裕介)
///
/// Copyright (C) 2018 Yusuke Matsunaga
/// All rights reserved.


#include "gtest/gtest.h"
#include "ym/FraigMgr.h"
#include "ym/BnNetwork.h"
#include "ym/Range.h"


BEGIN_NAMESPACE_FRAIG

TEST(EquivTest, EquivTest1)
{
  string filename1 = "C499.blif";
  string path1 = DATAPATH + filename1;
  BnNetwork network1 = BnNetwork::read_blif(path1);
  ASSERT_TRUE( network1.node_num() != 0 );

  int ni = network1.input_num();
  int no = network1.output_num();

  string filename2 = "C1355.blif";
  string path2 = DATAPATH + filename2;
  BnNetwork network2 = BnNetwork::read_blif(path2);
  ASSERT_TRUE( network2.node_num() != 0 );
  ASSERT_TRUE( network2.input_num() == ni );
  ASSERT_TRUE( network2.output_num() == no );

  FraigMgr mgr(1000);

  vector<FraigHandle> input_handles(ni);
  for ( int i: Range<>(ni) ) {
    input_handles[i] = mgr.make_input();
  }

  vector<FraigHandle> output_handles1(no);
  mgr.import_subnetwork(network1, input_handles, output_handles1);

  vector<FraigHandle> output_handles2(no);
  mgr.import_subnetwork(network2, input_handles, output_handles2);

  for ( int i: Range<>(no) ) {
    SatBool3 stat = mgr.check_equiv(output_handles1[i], output_handles2[i]);
    EXPECT_EQ( SatBool3::True, stat );
  }
}

END_NAMESPACE_FRAIG
