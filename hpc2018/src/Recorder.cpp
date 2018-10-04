//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Recorder.hpp"

//------------------------------------------------------------------------------
#include "ArrayNum.hpp"
#include "Print.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Recorder::Recorder()
: mGameRecord()
, mCurrentStageNumber()
, mCurrentTurn()
, mCurrentScore()
{
}

//------------------------------------------------------------------------------
void Recorder::dumpJson() const
{
    // Json の先頭
    HPC_PRINTF("["); {
        // 合計ターン数、スコア
        HPC_PRINTF("%d,", mGameRecord.totalTurn);
        HPC_PRINTF("%d,", mGameRecord.totalScore);
        // 定数
        HPC_PRINTF("["); {
            HPC_PRINTF("%d", Parameter::GameTurnLimit);
        } HPC_PRINTF("],");
        // ステージログ
        HPC_PRINTF("["); {
            for (int i = 0; i < Parameter::GameStageCount; ++i) {
                if(i != 0) {
                    HPC_PRINTF(",");
                }
                dumpJsonStage(mGameRecord.stageRecords[i]);
            }
        } HPC_PRINTF("]");
    } HPC_PRINTF("]");

    HPC_PRINTF("\n");
}

//------------------------------------------------------------------------------
void Recorder::dumpResult(bool aIsSilent) const
{
    if (!aIsSilent) {
        HPC_PRINTF("stage | score\n");
        for (int i = 0; i < Parameter::GameStageCount; ++i) {
            HPC_PRINTF("% 5d | % 4d\n", i, mGameRecord.stageRecords[i].score);
        }
    }
    HPC_PRINTF("TotalScore: %d\n", mGameRecord.totalScore);
}

//------------------------------------------------------------------------------
void Recorder::afterInitStage(const Stage& aStage)
{
    StageRecord& stageRecord = mGameRecord.stageRecords[mCurrentStageNumber];

    mCurrentTurn = 0;
    mCurrentScore = 0;
    stageRecord.score = 0;
    stageRecord.turnRecordCount = 0;

    stageRecord.ovenRecipeRecord.width = aStage.oven().width();
    stageRecord.ovenRecipeRecord.height = aStage.oven().height();

    writeTurnRecord(mCurrentStageNumber, 0, aStage);
}

//------------------------------------------------------------------------------
void Recorder::afterAdvanceTurn(const Stage& aStage)
{
    ++mCurrentTurn;
    writeTurnRecord(mCurrentStageNumber, mCurrentTurn, aStage);
}

//------------------------------------------------------------------------------
void Recorder::afterFinishStage()
{
    StageRecord& stageRecord = mGameRecord.stageRecords[mCurrentStageNumber];

    //  + 1 しているのは
    // レコードにはステージの初期状態が「0ターン目」として入っているから。
    stageRecord.turnRecordCount = mCurrentTurn + 1;
    stageRecord.score = mCurrentScore;
    mGameRecord.totalTurn += mCurrentTurn;
    mGameRecord.totalScore += mCurrentScore;
    ++mCurrentStageNumber;
}

//------------------------------------------------------------------------------
void Recorder::afterFinishAllStages()
{
    int total = 0;
    for (int i = 0; i < Parameter::GameStageCount; ++i) {
        total += mGameRecord.stageRecords[i].score;
    }
    HPC_ASSERT(total == mGameRecord.totalScore);
}

//------------------------------------------------------------------------------
int Recorder::totalTurn() const
{
    return mGameRecord.totalTurn;
}

//------------------------------------------------------------------------------
int Recorder::totalScore() const
{
    return mGameRecord.totalScore;
}

//------------------------------------------------------------------------------
Recorder::PieceRecord& Recorder::PieceRecord::setup(const Oven* aOven, const Piece& aPiece)
{
    if (aOven == nullptr) {
        fieldType = FieldType_Candidate;
    } else {
        fieldType = FieldType_Oven;
    }
    posX = static_cast<char>(aPiece.pos().x);
    posY = static_cast<char>(aPiece.pos().y);
    width = static_cast<char>(aPiece.width());
    height = static_cast<char>(aPiece.height());
    currentHeatTurnCount = static_cast<short>(aPiece.currentHeatTurnCount());
    requiredHeatTurnCount = static_cast<short>(aPiece.requiredHeatTurnCount());
    score = static_cast<short>(aPiece.score());
    return *this;
}

//------------------------------------------------------------------------------
void Recorder::PieceRecord::dumpJson() const
{
    HPC_PRINTF("["); {
        // 置いた位置
        HPC_PRINTF("["); {
            HPC_PRINTF("%d,%d", int(posX), int(posY));
        } HPC_PRINTF("],");

        // 縦横
        HPC_PRINTF("%d,", int(width));
        HPC_PRINTF("%d,", int(height));

        // 加熱ターン数関係
        HPC_PRINTF("%d,", int(currentHeatTurnCount));
        HPC_PRINTF("%d,", int(requiredHeatTurnCount));

        // 焼き上がりで発生するスコア
        HPC_PRINTF("%d", int(score));
    } HPC_PRINTF("]");
}

//------------------------------------------------------------------------------
Recorder::PieceRecord& Recorder::OvenRecord::bakingPieces(int aIndex)
{
    if (0 <= aIndex && aIndex < bakingPieceCount) {
        return prvBakingPieces[aIndex];
    }
    HPC_ASSERT_NOT_REACHED_MSG(
        "0 <= index:%d < bakingPieceCount:%d, failed",
        aIndex,
        bakingPieceCount
        );
    return prvBakingPieces[0];
}

//------------------------------------------------------------------------------
const Recorder::PieceRecord& Recorder::OvenRecord::bakingPieces(int aIndex) const
{
    if (0 <= aIndex && aIndex < bakingPieceCount) {
        return prvBakingPieces[aIndex];
    }
    HPC_ASSERT_NOT_REACHED_MSG(
        "0 <= index:%d < bakingPieceCount:%d, failed",
        aIndex,
        bakingPieceCount
        );
    return prvBakingPieces[0];
}

//------------------------------------------------------------------------------
Recorder::PieceRecord& Recorder::OvenRecord::bakedPieces(int aIndex)
{
    if (0 <= aIndex && aIndex < bakedPieceCount) {
        return prvBakedPieces[aIndex];
    }
    HPC_ASSERT_NOT_REACHED_MSG(
        "0 <= index:%d < bakedPieceCount:%d, failed",
        aIndex,
        bakedPieceCount
        );
    return prvBakedPieces[0];
}

//------------------------------------------------------------------------------
const Recorder::PieceRecord& Recorder::OvenRecord::bakedPieces(int aIndex) const
{
    if (0 <= aIndex && aIndex < bakedPieceCount) {
        return prvBakedPieces[aIndex];
    }
    HPC_ASSERT_NOT_REACHED_MSG(
        "0 <= index:%d < bakedPieceCount:%d, failed",
        aIndex,
        bakedPieceCount
        );
    return prvBakedPieces[0];
}

//------------------------------------------------------------------------------
int Recorder::StageRecord::turn() const
{
    //  - 1 しているのは
    // レコードにはステージの初期状態が「0ターン目」として入っているから。
    return turnRecordCount - 1;
}

//------------------------------------------------------------------------------
void Recorder::dumpJsonStage(const StageRecord& aRecord) const
{
    HPC_PRINTF("["); {
        // ターン数、スコア
        HPC_PRINTF("%d,", aRecord.turn());
        HPC_PRINTF("%d,", aRecord.score);

        // ステージ情報
        HPC_PRINTF("["); {
            // オーブン全体情報
            HPC_PRINTF("["); {
                // オーブン個体情報
                HPC_PRINTF("["); {
                    HPC_PRINTF("%d,", int(aRecord.ovenRecipeRecord.width));
                    HPC_PRINTF("%d,", int(aRecord.ovenRecipeRecord.height));
                    HPC_PRINTF("%d", 1); ///< オーブンの加熱速度(1で固定)
                } HPC_PRINTF("]");
            } HPC_PRINTF("]");
        } HPC_PRINTF("],");

        // ターンのログ
        HPC_PRINTF("["); {
            for (int i = 0; i < aRecord.turnRecordCount; ++i) {
                if (i != 0) {
                    HPC_PRINTF(",");
                }
                dumpJsonTurn(aRecord.turnRecords[i]);
            }
        } HPC_PRINTF("]");
    } HPC_PRINTF("]");
}

//------------------------------------------------------------------------------
void Recorder::dumpJsonTurn(const TurnRecord& aRecord) const
{
    HPC_PRINTF("["); {
        // このターンで生じたスコア
        HPC_PRINTF("%d,", aRecord.turnScore);
        // このターン終了時のスコア
        HPC_PRINTF("%d,", aRecord.turnEndScore);

        // 生地置き場
        HPC_PRINTF("["); {
            for (int laneType = 0; laneType < CandidateLaneType_TERM; ++laneType) {
                if (laneType != 0) {
                    HPC_PRINTF(",");
                }
                HPC_PRINTF("["); {
                    for (int i = 0; i < aRecord.candidatePieceCount[laneType]; ++i) {
                        if (i != 0) {
                            HPC_PRINTF(",");
                        }
                        // 生地
                        aRecord.candidateLane[laneType][i].dumpJson();
                    }
                } HPC_PRINTF("]");
            }
        } HPC_PRINTF("],");

        // オーブン
        HPC_PRINTF("["); {
            HPC_PRINTF("["); {
                const auto& ovenRecord = aRecord.ovenRecord;
                // このオーブンがこのターン終了時に獲得したスコア
                HPC_PRINTF("%d,", ovenRecord.turnScore);

                // 焼いている生地
                HPC_PRINTF("["); {
                    for (
                        int pieceIndex = 0;
                        pieceIndex < ovenRecord.bakingPieceCount;
                        ++pieceIndex)
                    {
                        if (pieceIndex != 0) {
                            HPC_PRINTF(",");
                        }
                        ovenRecord.bakingPieces(pieceIndex).dumpJson();
                    }
                } HPC_PRINTF("],");

                // このターン終了時に焼き上がった生地
                HPC_PRINTF("["); {
                    for (
                        int pieceIndex = 0;
                        pieceIndex < ovenRecord.bakedPieceCount;
                        ++pieceIndex)
                    {
                        if (pieceIndex != 0) {
                            HPC_PRINTF(",");
                        }
                        ovenRecord.bakedPieces(pieceIndex).dumpJson();
                    }
                } HPC_PRINTF("]");
            } HPC_PRINTF("]");
        } HPC_PRINTF("]");
    } HPC_PRINTF("]");
}

//------------------------------------------------------------------------------
void Recorder::writeTurnRecord(int aStageNumber, int aTurn, const Stage& aStage)
{
    TurnRecord& turnRecord =
        mGameRecord.stageRecords[aStageNumber].turnRecords[aTurn];

    // 初期化
    for (int laneType = 0; laneType < CandidateLaneType_TERM; ++laneType) {
        turnRecord.candidatePieceCount[laneType] = 0;
    }
    turnRecord.turnScore = 0;

    // 生地置き場
    for (int laneType = 0; laneType < CandidateLaneType_TERM; ++laneType) {
        const auto& lane = aStage.candidateLane(static_cast<CandidateLaneType>(laneType));
        turnRecord.candidatePieceCount[laneType] = lane.pieces().count();
        for (
            int pieceIndex = 0;
            pieceIndex < turnRecord.candidatePieceCount[laneType];
            ++pieceIndex
            )
        {
            const Piece& piece = lane.pieces()[pieceIndex];
            turnRecord.candidateLane[laneType][pieceIndex].setup(nullptr, piece);
        }
    }

    // オーブン
    {
        const Oven& oven = aStage.oven();
        OvenRecord& ovenRecord = turnRecord.ovenRecord;
        {
            // 焼いているもの
            const int pieceCount = oven.bakingPieces().count();
            ovenRecord.bakingPieceCount = pieceCount;
            for (int pieceIndex = 0; pieceIndex < pieceCount; ++pieceIndex) {
                const Piece& piece = oven.bakingPieces()[pieceIndex];
                ovenRecord.bakingPieces(pieceIndex).setup(&oven, piece);
            }
        }
        {
            // このターン焼けたもの
            const int pieceCount = oven.lastBakedPieces().count();
            ovenRecord.bakedPieceCount = pieceCount;
            ovenRecord.turnScore = 0;
            for (int pieceIndex = 0; pieceIndex < pieceCount; ++pieceIndex) {
                const Piece& piece = oven.lastBakedPieces()[pieceIndex];
                auto score = ovenRecord.bakedPieces(pieceIndex).setup(&oven, piece).score;
                turnRecord.turnScore += score;
                ovenRecord.turnScore += score;
            }
        }
    }

    // スコア更新
    mCurrentScore += turnRecord.turnScore;
    turnRecord.turnEndScore = mCurrentScore;
}

} // namespace
// EOF
