//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "CandidateLane.hpp"

//------------------------------------------------------------------------------
#include "Math.hpp"
#include "Print.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
CandidateLane::CandidateLane()
: mRecipe()
, mCandidatePieces()
{
}

//------------------------------------------------------------------------------
CandidateLane::CandidateLane(const CandidateLaneRecipe& aRecipe)
: mRecipe(aRecipe)
, mCandidatePieces()
{
}

//------------------------------------------------------------------------------
CandidatePieces& CandidateLane::pieces()
{
    return mCandidatePieces;
}

//------------------------------------------------------------------------------
const CandidatePieces& CandidateLane::pieces() const
{
    return mCandidatePieces;
}

//------------------------------------------------------------------------------
const CandidateLaneRecipe& CandidateLane::recipe() const
{
    return mRecipe;
}

//------------------------------------------------------------------------------
void CandidateLane::fill(Random* aRandom)
{
    HPC_ASSERT(aRandom != nullptr);

    while (mCandidatePieces.count() < mRecipe.visiblePieceCount()) {
        // 外周の半分を決定して
        const int hpm =
            aRandom->randMinMax(
                mRecipe.minSampleEdgeLength() * 2,
                mRecipe.maxSampleEdgeLength() * 2
                );
        // 折る場所を決めて
        const float foldPosRatio =
            aRandom->randFloatMinTerm(
                mRecipe.foldPosRatioMin(),
                mRecipe.foldPosRatioTerm()
                );
        // w/h が確定
        const int w = Math::LimitMinMax(static_cast<int>(hpm * foldPosRatio), 1, hpm - 1);
        const int h = Math::LimitMinMax(hpm - w, 1, hpm - 1);
        // 原始スコアを確定
        const int primalScore =
            aRandom->randMinMax(
                mRecipe.minPrimalScore(),
                mRecipe.maxPrimalScore()
                );
        // スコアを確定
        const int score =
            static_cast<int>(
                primalScore *
                aRandom->randFloatMinTerm(
                    mRecipe.scoreCoeffMin(),
                    mRecipe.scoreCoeffTerm()
                    )
                );
        // 必要加熱ターン数を確定
        const int rhtc = primalScore / (w * h);
        mCandidatePieces.add(Piece(Vector2i::Zero(), w, h, rhtc, score));
    }
}

} // namespace
// EOF
