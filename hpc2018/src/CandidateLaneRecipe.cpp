//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "CandidateLaneRecipe.hpp"

//------------------------------------------------------------------------------
#include "Assert.hpp"
#include "Print.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
CandidateLaneRecipe::CandidateLaneRecipe()
: mMinSampleEdgeLength()
, mMaxSampleEdgeLength()
, mFoldPosRatioMin()
, mFoldPosRatioTerm()
, mMinPrimalScore()
, mMaxPrimalScore()
, mScoreCoeffMin()
, mScoreCoeffTerm()
, mVisiblePieceCount()
{
}

//------------------------------------------------------------------------------
CandidateLaneRecipe::CandidateLaneRecipe(
    int aMinSampleEdgeLength,
    int aMaxSampleEdgeLength,
    float aFoldPosRatioMin,
    float aFoldPosRatioTerm,
    int aMinPrimalScore,
    int aMaxPrimalScore,
    float aScoreCoeffMin,
    float aScoreCoeffTerm,
    int aVisiblePieceCount
    )
: mMinSampleEdgeLength(aMinSampleEdgeLength)
, mMaxSampleEdgeLength(aMaxSampleEdgeLength)
, mFoldPosRatioMin(aFoldPosRatioMin)
, mFoldPosRatioTerm(aFoldPosRatioTerm)
, mMinPrimalScore(aMinPrimalScore)
, mMaxPrimalScore(aMaxPrimalScore)
, mScoreCoeffMin(aScoreCoeffMin)
, mScoreCoeffTerm(aScoreCoeffTerm)
, mVisiblePieceCount(aVisiblePieceCount)
{
    HPC_ASSERT_GREATER_EQUAL_I(aMinSampleEdgeLength, 1);
    HPC_ASSERT_GREATER_EQUAL_I(aMaxSampleEdgeLength, 1);
}

//------------------------------------------------------------------------------
int CandidateLaneRecipe::minSampleEdgeLength() const
{
    return mMinSampleEdgeLength;
}

//------------------------------------------------------------------------------
int CandidateLaneRecipe::maxSampleEdgeLength() const
{
    return mMaxSampleEdgeLength;
}

//------------------------------------------------------------------------------
float CandidateLaneRecipe::foldPosRatioMin() const
{
    return mFoldPosRatioMin;
}

//------------------------------------------------------------------------------
float CandidateLaneRecipe::foldPosRatioTerm() const
{
    return mFoldPosRatioTerm;
}

//------------------------------------------------------------------------------
int CandidateLaneRecipe::minPrimalScore() const
{
    return mMinPrimalScore;
}

//------------------------------------------------------------------------------
int CandidateLaneRecipe::maxPrimalScore() const
{
    return mMaxPrimalScore;
}

//------------------------------------------------------------------------------
float CandidateLaneRecipe::scoreCoeffMin() const
{
    return mScoreCoeffMin;
}

//------------------------------------------------------------------------------
float CandidateLaneRecipe::scoreCoeffTerm() const
{
    return mScoreCoeffTerm;
}

//------------------------------------------------------------------------------
int CandidateLaneRecipe::visiblePieceCount() const
{
    return mVisiblePieceCount;
}

} // namespace
// EOF
