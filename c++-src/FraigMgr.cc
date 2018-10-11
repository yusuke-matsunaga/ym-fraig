
/// @file FraigMgr.cc
/// @brief FraigMgr の実装ファイル
/// @author Yusuke Matsunaga (松永 裕介)
///
/// Copyright (C) 2018 Yusuke Matsunaga
/// All rights reserved.


#include "ym/FraigMgr.h"
#include "FraigNode.h"
#include "ym/StopWatch.h"
#include "ym/SatStats.h"


#if defined(YM_DEBUG)
#define DEBUG_FLAG 1
#endif

#if !defined(DEBUG_FLAG)
#define DEBUG_FLAG 0
#endif


BEGIN_NAMESPACE_EQUIV

BEGIN_NONAMESPACE

const int debug = DEBUG_FLAG;

END_NONAMESPACE

//////////////////////////////////////////////////////////////////////
// FraigMgr
//////////////////////////////////////////////////////////////////////

// @brief コンストラクタ
// @brief sig_size シグネチャのサイズ
// @param[in] solver_type SAT-solver の種類を表すオブジェクト
FraigMgr::FraigMgr(int sig_size,
		   const SatSolverType& solver_type) :
  mRep(new FraigMgrImpl(sig_size, solver_type))
{
}

// @brief デストラクタ
FraigMgr::~FraigMgr()
{
}

// @brief 外部入力を作る．
FraigHandle
FraigMgr::make_input()
{
  return mRep->make_input();
}

// @brief 2つのノードの AND を取る．
// @param[in] handle1, handle2 入力の AIG ハンドル
FraigHandle
FraigMgr::make_and(FraigHandle handle1,
		   FraigHandle handle2)
{
  return mRep->make_and(handle1, handle2);
}

// @brief 論理式に対応するノード(木)をつくる．
// @param[in] expr 対象の論理式
// @param[in] inputs 入力に対応する AIG ハンドル
FraigHandle
FraigMgr::make_expr(const Expr& expr,
		    const vector<FraigHandle>& inputs)
{
  if ( expr.is_zero() ) {
    return make_zero();
  }
  if ( expr.is_one() ) {
    return make_one();
  }
  if ( expr.is_posi_literal() ) {
    VarId var = expr.varid();
    int id = var.val();
    ASSERT_COND(id < inputs.size() );
    return inputs[id];
  }
  if ( expr.is_nega_literal() ) {
    VarId var = expr.varid();
    int id = var.val();
    ASSERT_COND(id < inputs.size() );
    return ~inputs[id];
  }

  int n = expr.child_num();
  vector<FraigHandle> edge_list(n);
  for ( int i = 0; i < n; ++ i ) {
    edge_list[i] = make_expr(expr.child(i), inputs);
  }
  if ( expr.is_and() ) {
    return make_and(edge_list);
  }
  if ( expr.is_or() ) {
    return make_or(edge_list);
  }
  if ( expr.is_xor() ) {
    return make_xor(edge_list);
  }

  ASSERT_NOT_REACHED;
  return make_zero();
}

// @brief コファクターを計算する．
// @param[in] edge 対象の AIG ハンドル
// @param[in] input_id コファクターをとる入力番号
// @param[in] pol 極性
FraigHandle
FraigMgr::make_cofactor(FraigHandle edge,
			int input_id,
			bool inv)
{
  if ( edge.is_const() ) {
    // edge が定数の時は変更なし
    return edge;
  }

  FraigNode* node = edge.node();
  FraigHandle ans;
  if ( node->is_input() ) {
    // 入力ノード時は番号が input_id どうかで処理が変わる．
    if ( node->input_id() == input_id ) {
      if ( inv ) {
	ans = make_zero();
      }
      else {
	ans = make_one();
      }
    }
    else {
      ans = FraigHandle(node, false);
    }
  }
  else {
    // AND ノードの場合
    // 2つの子供に再帰的な処理を行って結果の AND を計算する．
    FraigHandle new_handle0 = make_cofactor(node->fanin0_handle(), input_id, inv);
    FraigHandle new_handle1 = make_cofactor(node->fanin1_handle(), input_id, inv);
    FraigHandle ans = make_and(new_handle0, new_handle1);
  }
  if ( edge.inv() ) {
    ans = ~ans;
  }
  return ans;
}

// @brief 複数のノードの AND を取る．
// @param[in] edge_list 入力の AIG ハンドルのリスト
// @param[in] start_pos 開始位置
// @param[in] end_pos 終了位置
// @param[in] iinv 入力の反転フラグ
//
// edge_list[start_pos] から edge_list[end_pos - 1] までの
// ハンドルの AND を取る．
// なので常に end_pos > start_pos が成り立つと仮定する．
FraigHandle
FraigMgr::_make_and(const vector<FraigHandle>& edge_list,
		    int start_pos,
		    int end_pos,
		    bool iinv)
{
  ASSERT_COND( start_pos < end_pos );

  int n = end_pos - start_pos;
  if ( n == 1 ) {
    FraigHandle h = edge_list[start_pos];
    if ( iinv ) {
      h = ~h;
    }
    return h;
  }
  // n >= 2
  int mid_pos = start_pos + (n + 1) / 2;
  FraigHandle h0 = _make_and(edge_list, start_pos, mid_pos, iinv);
  FraigHandle h1 = _make_and(edge_list, mid_pos, end_pos, iinv);
  return make_and(h0, h1);
}

// @brief 複数のノードの XOR を取る．
// @param[in] edge_list 入力の AIG ハンドルのリスト
// @param[in] start_pos 開始位置
// @param[in] end_pos 終了位置
//
// edge_list[start_pos] から edge_list[end_pos - 1] までの
// ハンドルの XOR を取る．
// なので常に end_pos > start_pos が成り立つと仮定する．
FraigHandle
FraigMgr::_make_xor(const vector<FraigHandle>& edge_list,
		    int start_pos,
		    int end_pos)
{
  ASSERT_COND( start_pos < end_pos );

  int n = end_pos - start_pos;
  if ( n == 1 ) {
    return edge_list[start_pos];
  }
  // n >= 2
  int mid_pos = start_pos + (n + 1) / 2;
  FraigHandle h0 = _make_xor(edge_list, start_pos, mid_pos);
  FraigHandle h1 = _make_xor(edge_list, mid_pos, end_pos);
  return make_xor(h0, h1);
}

// @brief 2つのハンドルが等価かどうか調べる．
SatBool3
FraigMgr::check_equiv(FraigHandle aig1,
		      FraigHandle aig2)
{
  return mRep->check_equiv(aig1, aig2);
}

// @brief ログレベルを設定する．
void
FraigMgr::set_loglevel(int level)
{
  mRep->set_loglevel(level);
}

// @brief ログ出力用ストリームを設定する．
void
FraigMgr::set_logstream(ostream* out)
{
  mRep->set_logstream(out);
}

// @brief ランダムシミュレーション制御用のパラメータを設定する．
void
FraigMgr::set_loop_limit(int val)
{
  mRep->set_loop_limit(val);
}

END_NAMESPACE_EQUIV
