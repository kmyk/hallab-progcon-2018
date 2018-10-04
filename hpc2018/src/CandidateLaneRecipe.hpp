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
namespace hpc {

/// 生地置き場を構築するためのレシピ。
class CandidateLaneRecipe
{
public:
    /// @name コンストラクタ
    //@{
    CandidateLaneRecipe();
    CandidateLaneRecipe(
        int aMinSampleEdgeLength,
        int aMaxSampleEdgeLength,
        float aFoldPosRatioMin,
        float aFoldPosRatioTerm,
        int aMinPrimalScore,
        int aMaxPrimalScore,
        float aScoreCoeffMin,
        float aScoreCoeffTerm,
        int aVisiblePieceCount
        );
    //@}

    /// @name 問い合わせ
    //@{
    /// 基準正方形の一辺の長さの最小値。
    int minSampleEdgeLength() const;
    /// 基準正方形の一辺の長さの最大値。
    int maxSampleEdgeLength() const;
    /// 生地の長辺＋短辺を折る位置の最小値。
    float foldPosRatioMin() const;
    /// 生地の長辺＋短辺を折る位置の最大値。
    float foldPosRatioTerm() const;
    /// 原始スコアの最小値。
    int minPrimalScore() const;
    /// 原始スコアの最大値。
    int maxPrimalScore() const;
    /// スコア換算係数の最小値。
    float scoreCoeffMin() const;
    /// スコア換算係数の最大値。
    float scoreCoeffTerm() const;
    /// 見えている生地の最大数。
    int visiblePieceCount() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// 基準正方形の一辺の長さの最小値。
    int mMinSampleEdgeLength;
    /// 基準正方形の一辺の長さの最大値。
    int mMaxSampleEdgeLength;
    /// 生地の長辺＋短辺を折る位置の最小値。
    float mFoldPosRatioMin;
    /// 生地の長辺＋短辺を折る位置の最大値。
    float mFoldPosRatioTerm;
    /// 原始スコアの最小値。
    int mMinPrimalScore;
    /// 原始スコアの最大値。
    int mMaxPrimalScore;
    /// スコア換算係数の最小値。
    float mScoreCoeffMin;
    /// スコア換算係数の最大値。
    float mScoreCoeffTerm;
    /// 見えている生地の最大数。
    int mVisiblePieceCount;
    //@}
};

} // namespace
// EOF
