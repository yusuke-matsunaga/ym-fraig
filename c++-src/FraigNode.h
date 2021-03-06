﻿#ifndef FRAIGNODE_H
#define FRAIGNODE_H

/// @file FraigNode.h
/// @brief FraigNode のヘッダファイル
/// @author Yusuke Matsunaga (松永 裕介)
///
/// Copyright (C) 2018 Yusuke Matsunaga
/// All rights reserved.


#include "ym/fraig.h"
#include "ym/FraigHandle.h"


BEGIN_NAMESPACE_FRAIG

//////////////////////////////////////////////////////////////////////
/// @class FraigNode FraigNode.h "FraigNode.h"
/// @brief Fraig のノードを表すクラス
//////////////////////////////////////////////////////////////////////
class FraigNode
{
  friend class FraigMgrImpl;
  friend class StructHash;
  friend class PatHash;

public:

  /// @brief コンストラクタ
  FraigNode();

  /// @brief デストラクタ
  ~FraigNode();


public:
  //////////////////////////////////////////////////////////////////////
  // 内容を設定する関数
  //////////////////////////////////////////////////////////////////////

  /// @brief 入力番号をセットする．
  void
  set_input(int id);

  /// @brief ファンインをセットする．
  /// @param[in] handle1, handle2 ファンインのハンドル
  void
  set_fanin(FraigHandle handle1,
	    FraigHandle handle2);



public:
  //////////////////////////////////////////////////////////////////////
  // 変数番号に関するアクセス関数
  //////////////////////////////////////////////////////////////////////

  /// @brief CNF 上の変数番号を返す．
  SatLiteral
  varid() const;


public:
  //////////////////////////////////////////////////////////////////////
  // 入力ノードの時のアクセス関数
  //////////////////////////////////////////////////////////////////////

  /// @brief 入力ノードの時に true を返す．
  bool
  is_input() const;

  /// @brief 入力番号を返す．
  int
  input_id() const;


public:
  //////////////////////////////////////////////////////////////////////
  // AND ノードの時のアクセス関数
  //////////////////////////////////////////////////////////////////////

  /// @brief AND の時に true を返す．
  bool
  is_and() const;

  /// @brief ファンインを得る．
  /// @param[in] pos 位置 ( 0 or 1 )
  FraigNode*
  fanin(int pos) const;

  /// @brief 1番めのファンインを得る．
  FraigNode*
  fanin0() const;

  /// @brief 2番めのファンインを得る．
  FraigNode*
  fanin1() const;

  /// @brief ファンインの極性を得る．
  /// @param[in] pos 位置 ( 0 or 1 )
  bool
  fanin_inv(int pos) const;

  /// @brief 1番めのファンインの極性を得る．
  bool
  fanin0_inv() const;

  /// @brief 2番めのファンインの極性を得る．
  bool
  fanin1_inv() const;

  /// @brief ファンインのハンドルを得る．
  /// @param[in] pos 位置 ( 0 or 1 )
  FraigHandle
  fanin_handle(int pos) const;

  /// @brief 1番め初のファンインのハンドルを得る．
  FraigHandle
  fanin0_handle() const;

  /// @brief 2番めのファンインのハンドルを得る．
  FraigHandle
  fanin1_handle() const;


public:
  //////////////////////////////////////////////////////////////////////
  // シミュレーション・パタンに関するアクセス関数
  //////////////////////////////////////////////////////////////////////

  /// @brief パタンをセットする．
  /// @param[in] start 開始位置
  /// @param[in] end 終了位置
  /// @param[in] pat パタンのベクタ
  void
  set_pat(int start,
	  int end,
	  const vector<ymuint64>& pat);

  /// @brief パタンを計算する．
  /// @param[in] start 開始位置
  /// @param[in] end 終了位置
  /// @note ANDノード用
  void
  calc_pat(int start,
	   int end);

  /// @brief 0 の値を取るとき true を返す．
  bool
  check_0mark() const;

  /// @brief 1 の値を取るとき true を返す．
  bool
  check_1mark() const;

  /// @brief パタンのハッシュ値を返す．
  SizeType
  pat_hash() const;

  /// @brief ハッシュ値の極性を返す．
  bool
  pat_hash_inv() const;


public:
  //////////////////////////////////////////////////////////////////////
  // 等価グループに関するアクセス関数
  //////////////////////////////////////////////////////////////////////

  /// @brief 削除済みのとき true を返す．
  bool
  check_dmark() const;

  /// @brief 要素数が2以上の等価候補グループの代表なら true を返す．
  bool
  check_rep() const;

  /// @brief 代表ノードを返す．
  FraigNode*
  rep_node() const;

  /// @brief 代表ノードに対する極性を返す．
  bool
  rep_inv() const;

  /// @brief 代表ノードを返す．
  FraigHandle
  rep_handle() const;

  /// @brief 次の等価候補ノードを得る．
  FraigNode*
  next_eqnode();

  /// @brief 等価候補の代表にする．
  void
  set_rep(FraigNode* rep_node,
	  bool inv);

  /// @brief 極性反転の印をつける．
  void
  set_rep_inv();

  /// @brief 等価候補ノードを追加する．
  void
  add_eqnode(FraigNode* node);

  /// @brief 削除済みの印をつける．
  void
  set_dmark();


public:
  //////////////////////////////////////////////////////////////////////
  // ハッシュ用のリンクアクセス関数
  //////////////////////////////////////////////////////////////////////

  FraigNode*&
  link(int link_pos);


private:
  //////////////////////////////////////////////////////////////////////
  // 下請け関数
  //////////////////////////////////////////////////////////////////////

  /// @brief ハッシュ値を計算する．
  /// @param[in] start 開始位置
  /// @param[in] end 終了位置
  void
  calc_hash(int start,
	    int end);

  /// @brief 0 の値を取ったことを記録する．
  void
  set_0mark();

  /// @brief 1 の値を取ったことを記録する．
  void
  set_1mark();


private:
  //////////////////////////////////////////////////////////////////////
  // データメンバ
  //////////////////////////////////////////////////////////////////////

  // CNF 上の変数番号
  SatLiteral mVarId;

  // ファンインのノード
  FraigNode* mFanins[2];

  // 0/1マーク，極性などの情報をパックしたもの
  ymuint32 mFlags;

  // シミュレーションパタン
  ymuint64* mPat;

  // mPat のハッシュ値
  SizeType mHash;

  // 構造ハッシュ用のリンクポインタ
  FraigNode* mLink1;

  // シグネチャハッシュ用のリンクポインタ
  FraigNode* mLink2;

  // 代表ノード情報
  FraigNode* mRepNode;

  // 次の等価候補ノード
  FraigNode* mEqLink;

  // 等価候補リストの末尾のノード
  FraigNode* mEqTail;


private:
  //////////////////////////////////////////////////////////////////////
  // クラスメンバ
  //////////////////////////////////////////////////////////////////////

  // ハッシュ用の素数配列
  static
  ymuint64 mPrimes[];


private:
  //////////////////////////////////////////////////////////////////////
  // mFlags で用いるシフト定数
  //////////////////////////////////////////////////////////////////////

  // 入力フラグ
  static
  const int kSftI  = 0;

  // ファンイン0 の極性
  static
  const int kSftP0 = 1;

  // ファンイン1 の極性
  static
  const int kSftP1 = 2;

  // 0 になったことがあるかどうか
  static
  const int kSft0  = 3;

  // 1 になったことがあるかどうか
  static
  const int kSft1  = 4;

  // ハッシュパタンの極性
  static
  const int kSftH  = 5;

  // 等価グループ中の極性
  static
  const int kSftP  = 6;

  // 削除マーク
  static
  const int kSftD  = 7;

};


//////////////////////////////////////////////////////////////////////
// インライン関数の定義
//////////////////////////////////////////////////////////////////////

// @brief CNF 上の変数番号を返す．
inline
SatLiteral
FraigNode::varid() const
{
  return mVarId;
}

// @brief 入力ノードの時に true を返す．
inline
bool
FraigNode::is_input() const
{
  return static_cast<bool>((mFlags >> kSftI) & 1U);
}

// @brief 入力番号を返す．
inline
int
FraigNode::input_id() const
{
  return reinterpret_cast<ympuint>(mFanins[0]);
}

// @brief 入力番号をセットする．
inline
void
FraigNode::set_input(int id)
{
  mFlags |= (1U << kSftI);
  mFanins[0] = reinterpret_cast<FraigNode*>(id);
}

// @brief AND の時に true を返す．
inline
bool
FraigNode::is_and() const
{
  return !is_input();
}

// @brief ファンインを得る．
inline
FraigNode*
FraigNode::fanin(int pos) const
{
  // 安全のため pos の値を補正しておく．
  pos &= 1;
  return mFanins[pos];
}

// @brief 最初のファンインを得る．
inline
FraigNode*
FraigNode::fanin0() const
{
  return mFanins[0];
}

// @brief 2番めのファンインを得る．
inline
FraigNode*
FraigNode::fanin1() const
{
  return mFanins[1];
}

// @brief ファンインの極性を得る．
inline
bool
FraigNode::fanin_inv(int pos) const
{
  // 安全のため pos の値を補正しておく．
  pos &= 1;
  return static_cast<bool>((mFlags >> (kSftP0 + pos)) & 1U);
}

// @brief 最初のファンインの極性を得る．
inline
bool
FraigNode::fanin0_inv() const
{
  return static_cast<bool>((mFlags >> kSftP0) & 1U);
}

// @brief 2番めのファンインの極性を得る．
inline
bool
FraigNode::fanin1_inv() const
{
  return static_cast<bool>((mFlags >> kSftP1) & 1U);
}

// @brief ファンインのハンドルを得る．
inline
FraigHandle
FraigNode::fanin_handle(int pos) const
{
  // 安全のため pos の値を補正しておく．
  pos &= 1;
  return FraigHandle(fanin(pos), fanin_inv(pos));
}

// @brief 最初のファンインのハンドルを得る．
inline
FraigHandle
FraigNode::fanin0_handle() const
{
  return FraigHandle(fanin0(), fanin0_inv());
}

// @brief 2番めのファンインのハンドルを得る．
inline
FraigHandle
FraigNode::fanin1_handle() const
{
  return FraigHandle(fanin1(), fanin1_inv());
}

// @brief 0 の値を取るとき true を返す．
inline
bool
FraigNode::check_0mark() const
{
  return static_cast<bool>((mFlags >> kSft0) & 1U);
}

// @brief 1 の値を取るとき true を返す．
inline
bool
FraigNode::check_1mark() const
{
  return static_cast<bool>((mFlags >> kSft1) & 1U);
}

// @brief パタンのハッシュ値を返す．
inline
SizeType
FraigNode::pat_hash() const
{
  return mHash;
}

// @brief ハッシュ値の極性を返す．
inline
bool
FraigNode::pat_hash_inv() const
{
  return static_cast<bool>((mFlags >> kSftH) & 1U);
}

// @brief 削除済みのとき true を返す．
inline
bool
FraigNode::check_dmark() const
{
  return static_cast<bool>((mFlags >> kSftD) & 1U);
}

// @brief 要素数が2以上の等価候補グループの代表なら true を返す．
inline
bool
FraigNode::check_rep() const
{
  return mRepNode == this && mEqLink != nullptr;
}

// @brief 代表ノードを返す．
inline
FraigNode*
FraigNode::rep_node() const
{
  return mRepNode;
}

// @brief 代表ノードに対する極性を返す．
inline
bool
FraigNode::rep_inv() const
{
  return static_cast<bool>((mFlags >> kSftP) & 1U);
}

// @brief 代表ノードを返す．
inline
FraigHandle
FraigNode::rep_handle() const
{
  return FraigHandle(mRepNode, rep_inv());
}

// @brief 次の等価候補ノードを得る．
inline
FraigNode*
FraigNode::next_eqnode()
{
  return mEqLink;
}

// @brief 代表ノードをセットする．
inline
void
FraigNode::set_rep(FraigNode* rep_node,
		   bool inv)
{
  mRepNode = rep_node;
  if ( inv ) {
    set_rep_inv();
  }
}

// @brief 等価候補ノードを追加する．
inline
void
FraigNode::add_eqnode(FraigNode* node)
{
  mEqTail->mEqLink = node;
  mEqTail = node;
  node->mRepNode = this;
  node->mEqLink = nullptr;
}

// @brief 0 の値を取ったことを記録する．
inline
void
FraigNode::set_0mark()
{
  mFlags |= (1U << kSft0);
}

// @brief 1 の値を取ったことを記録する．
inline
void
FraigNode::set_1mark()
{
  mFlags |= (1U << kSft1);
}

// @brief 極性反転の印をつける．
inline
void
FraigNode::set_rep_inv()
{
  mFlags |= (1U << kSftP);
}

// @brief 削除済みの印をつける．
inline
void
FraigNode::set_dmark()
{
  mFlags |= (1U << kSftD);
}

// @brief パタンを計算する．
inline
void
FraigNode::calc_pat(int start,
		    int end)
{
  ymuint64* dst = mPat + start;
  ymuint64* dst_end = mPat + end;
  ymuint64* src1 = mFanins[0]->mPat + start;
  ymuint64* src2 = mFanins[1]->mPat + start;
  if ( fanin0_inv() ) {
    if ( fanin1_inv() ) {
      for ( ; dst != dst_end; ++ dst, ++src1, ++src2) {
	*dst = ~(*src1 | *src2);
      }
    }
    else {
      for ( ; dst != dst_end; ++ dst, ++src1, ++src2) {
	*dst = ~*src1 & *src2;
      }
    }
  }
  else {
    if ( fanin1_inv() ) {
      for ( ; dst != dst_end; ++ dst, ++src1, ++src2) {
	*dst = *src1 & ~*src2;
      }
    }
    else {
      for ( ; dst != dst_end; ++ dst, ++src1, ++src2) {
	*dst = *src1 & *src2;
      }
    }
  }
  calc_hash(start, end);
}

inline
FraigNode*&
FraigNode::link(int link_pos)
{
  return link_pos == 0 ? mLink1 : mLink2;
}

END_NAMESPACE_FRAIG

#endif // FRAIGNODE_H
