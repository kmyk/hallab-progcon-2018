//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Stage.hpp"

//------------------------------------------------------------------------------
#include <algorithm>
#include "ArrayNum.hpp"
#include "Assert.hpp"
#include "Math.hpp"
#include "Print.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Stage::Stage()
: mTurn()
, mScore()
, mOven()
, mCandidateLanes()
{
}

//------------------------------------------------------------------------------
int Stage::turn() const
{
    return mTurn;
}

//------------------------------------------------------------------------------
const Oven& Stage::oven() const
{
    return mOven;
}

//------------------------------------------------------------------------------
const CandidateLane& Stage::candidateLane(CandidateLaneType aType) const
{
    return mCandidateLanes[aType];
}

//------------------------------------------------------------------------------
void Stage::init(const RandomSeed& aStageRandomSeed, CandidateLaneRandoms* aLaneRandoms)
{
    Random random(aStageRandomSeed);

    mTurn = 0;
    mScore = 0;
    mOven = Oven(OvenRecipe(Parameter::OvenWidth, Parameter::OvenHeight));

    {
        // 乱数取得を関数引数に直接置くのはアウト。
        // 環境に依って引数の評価順序が異なるので、
        // ことなる数値で動くことになってしまう。

        // PieceFoldPosRate
        const float fprCenter =
            random.randFloatMinTerm(
                Parameter::MinPieceFoldPosRateCenter,
                Parameter::MaxPieceFoldPosRateCenter
                );
        const float fprRange =
            random.randFloatMinTerm(
                Parameter::MinPieceFoldPosRateRange,
                Parameter::MaxPieceFoldPosRateRange
                );

        // SampleEdgeLength
        int selMin = 1;
        int selMax = 1;

        // PrimalScore
        int psMin = 1;
        int psMax = 1;

        // ScoreCoeff
        float scoreCoeffCenter = 1.0f;
        float scoreCoeffRange = 0.0f;

        // 各生地置き場を生成
        for (int laneType = 0; laneType < CandidateLaneType_TERM; ++laneType) {
            switch (laneType) {
                case CandidateLaneType_Small:
                    selMin = Parameter::MinSmallPieceSampleEdgeLength;
                    selMax = Parameter::MaxSmallPieceSampleEdgeLength;
                    psMin = Parameter::MinSmallPiecePrimalScore;
                    psMax = Parameter::MaxSmallPiecePrimalScore;
                    scoreCoeffCenter = Parameter::SmallPieceScoreCoeffCenter;
                    scoreCoeffRange = Parameter::SmallPieceScoreCoeffRange;
                    break;
                case CandidateLaneType_Large:
                    selMin = Parameter::MinLargePieceSampleEdgeLength;
                    selMax = Parameter::MaxLargePieceSampleEdgeLength;
                    psMin = Parameter::MinLargePiecePrimalScore;
                    psMax = Parameter::MaxLargePiecePrimalScore;
                    scoreCoeffCenter =
                        random.randFloatMinTerm(
                            Parameter::MinLargePieceScoreCoeffCenter,
                            Parameter::MaxLargePieceScoreCoeffCenter
                            );
                    scoreCoeffRange = Parameter::LargePieceScoreCoeffRange;
                    break;
                default:
                    HPC_ASSERT_NOT_REACHED_MSG("unknown laneType:%d", laneType);
                    break;
            }

            CandidateLaneRecipe recipe(
                selMin,
                selMax,
                Math::LimitMinMax(fprCenter - fprRange / 2, 0.0f, 1.0f),
                Math::LimitMinMax(fprCenter + fprRange / 2, 0.0f, 1.0f),
                psMin,
                psMax,
                Math::Max(scoreCoeffCenter - scoreCoeffRange / 2, 0.0f),
                Math::Max(scoreCoeffCenter + scoreCoeffRange / 2, 0.0f),
                Parameter::CandidatePieceCount
                );
            mCandidateLanes.add(CandidateLane(recipe));
        }
    }
    fillCandidate(aLaneRandoms);
}

//------------------------------------------------------------------------------
void Stage::processStartPhase()
{
    addHeatTurnCount(1);
}

//------------------------------------------------------------------------------
void Stage::processPlayerPhase(const Action& aAction)
{
    switch (aAction.type()) {
        case ActionType_Wait: processPlayerPhaseWait(aAction); break;
        case ActionType_Put: processPlayerPhasePut(aAction); break;
        default:
            HPC_ASSERT_NOT_REACHED_MSG("Unknown type:%d", aAction.type());
            break;
    }
}

//------------------------------------------------------------------------------
void Stage::processEndPhase(CandidateLaneRandoms* aLaneRandoms)
{
    mScore += gatherBaked();
    // ターン開始時に生地置き場チャージすると
    // 生地置き場チャージから生地Putまでの間にターン記録処理が入らないので、
    // 生地が 1 記録ターン未満の速度で配置されることになり、ビューアで観測できなくなる。
    // 対処として生地置き場チャージを終了フェーズで行うようにして、
    // 生地置き場チャージとその配置の間に確実にターン記録処理が挟まるようにする。
    fillCandidate(aLaneRandoms);
}

//------------------------------------------------------------------------------
void Stage::advanceTurn()
{
    ++mTurn;
}

//------------------------------------------------------------------------------
bool Stage::isEnd() const
{
    // 生地は無限に供給されるので、ステージが自力で終了することはない。
    // ターン数によるステージ終了処理は Game で実装されている。
    return false;
}

//------------------------------------------------------------------------------
void Stage::fillCandidate(CandidateLaneRandoms* aLaneRandoms)
{
    for (int laneType = 0; laneType < CandidateLaneType_TERM; ++laneType) {
        auto& lane = mCandidateLanes[laneType];
        auto& random = (*aLaneRandoms)[laneType];
        lane.fill(&random);
    }
}

//------------------------------------------------------------------------------
void Stage::addHeatTurnCount(int aTurnCount)
{
    mOven.addHeatTurnCount(aTurnCount);
}

//------------------------------------------------------------------------------
int Stage::gatherBaked()
{
    int subScore = 0;
    mOven.clearLastBakedPieces();
    subScore += mOven.gatherBaked();
    return subScore;
}

//------------------------------------------------------------------------------
void Stage::processPlayerPhaseWait(const Action&)
{
    // 何もしない
}

//------------------------------------------------------------------------------
void Stage::processPlayerPhasePut(const Action& aAction)
{
    if (
        0 <= aAction.candidateLaneType() &&
        aAction.candidateLaneType() < mCandidateLanes.count()
        )
    {
    } else {
        // 生地置き場の指定が範囲外
        HPC_ASSERT_NOT_REACHED_MSG(
            "0 <= laneType:%d < laneCount:%d, failed",
            aAction.candidateLaneType(),
            mCandidateLanes.count()
            );
        // 何もしない
        return;
    }

    auto& lane = mCandidateLanes[aAction.candidateLaneType()];

    if (0 <= aAction.pieceIndex() && aAction.pieceIndex() < lane.pieces().count()) {
    } else {
        // 記事番号指定が範囲外
        HPC_ASSERT_NOT_REACHED_MSG(
            "0 <= pieceIndex:%d < candidateCount:%d, failed",
            aAction.pieceIndex(),
            lane.pieces().count()
            );
        // 何もしない
        return;
    }

    auto& piece = lane.pieces()[aAction.pieceIndex()];

    if (mOven.tryToBake(&piece, aAction.putPos())) {
        // 成功
    } else {
        // 生地配置位置が悪い(他生地と被っている、オーブンの天板をはみ出ている、など)
        // 何もしない
        return;
    }

    // 全部通過できていたら、
    // その生地はめでたくオーブンに入ったということ。
    // 生地置き場から生地を消す。
    lane.pieces().erase(aAction.pieceIndex());
}

} // namespace
// EOF
