//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
#include "Array.hpp"
#include "CandidateLaneRecipe.hpp"
#include "Parameter.hpp"
#include "Piece.hpp"
#include "Random.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// 生地の配列。
using CandidatePieces = Array<Piece, Parameter::CandidatePieceCount>;

/// 生地置き場。
class CandidateLane
{
public:
    /// @name コンストラクタ
    //@{
    CandidateLane();
    explicit CandidateLane(const CandidateLaneRecipe& aRecipe);
    //@}

    /// @name 生地情報
    //@{
    /// 生地置き場に置かれている生地一覧を取得する。
    CandidatePieces& pieces();
    /// 生地置き場に置かれている生地一覧を取得する。
    const CandidatePieces& pieces() const;
    //@}

    /// @name 設定
    //@{
    /// この生地置き場の設定情報を取得する。
    const CandidateLaneRecipe& recipe() const;
    //@}

    /// @name 内部用関数
    //@{
    /// 生地置き場がいっぱいになるまで、新しい生地を生成して詰め込む。
    void fill(Random* aRandom);
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    CandidateLaneRecipe mRecipe;
    CandidatePieces mCandidatePieces;
    //@}
};

} // namespace
// EOF
