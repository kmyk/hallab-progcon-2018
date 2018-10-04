//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Game.hpp"

//------------------------------------------------------------------------------
#include "Assert.hpp"
#include "Stage.hpp"

//------------------------------------------------------------------------------
namespace hpc {

//------------------------------------------------------------------------------
Game::Game()
: mIsRandomSeedSet(false)
, mGivenRandomSeed(RandomSeed::DefaultSeed())
, mRecorder()
, mTimer()
{
}

//------------------------------------------------------------------------------
void Game::changeSeed(RandomSeed aSeed)
{
    mIsRandomSeedSet = true;
    mGivenRandomSeed = aSeed;
}

//------------------------------------------------------------------------------
void Game::run(Answer* aAnswer)
{
    HPC_ASSERT(aAnswer != nullptr);

    // 乱数関連の定数定義。
    // ここの randomSeed および randomSpin は
    // サーバーの評価環境と配布パッケージとで異なります。
    const uint randomSeedX = 0x1c8bebfc;
    const uint randomSeedY = 0xdf7b3c3c;
    const uint randomSeedZ = 0x16bf5f2d;
    const uint randomSeedW = 0x5aee504a;
    const int randomSpinX = 0xFFF;
    const int randomSpinY = 0xFF;
    const int randomSpinZ = 0xF;

    Random gameRandom =
        Random(
            mIsRandomSeedSet ?
            mGivenRandomSeed :
            RandomSeed(
                randomSeedX,
                randomSeedY,
                randomSeedZ,
                randomSeedW
                )
            );

    // ゲーム開始
    mTimer.start();
    gameRandom.spin(randomSpinX);

    for (int i = 0; i < Parameter::GameStageCount; ++i) {
        // ステージ開始
        gameRandom.spin(randomSpinY);

        // 生地置き場専用の乱数。
        // 出現生地が生地置き場の使用順序に依存しないようにするために、
        // 各生地置き場は自前の乱数を持っている。
        // また、 Random はデフォルトコンストラクタを持たないので、
        // std::array で初期化するタイプの Array コンストラクタで
        // CandidateLaneRandoms を構築している。
        // 初期化子リストは先頭から評価されることが保証されているので、
        // generateRandomSeed をその場で使っている。
        CandidateLaneRandoms laneRandom(
            CandidateLaneRandoms::ArrayType(
                {{
                    Random(gameRandom.generateRandomSeed()),
                    Random(gameRandom.generateRandomSeed())
                }}
            )
        );

        // ステージ生成
        Stage stage;
        {
            auto randomSeed = gameRandom.generateRandomSeed();
            stage.init(randomSeed, &laneRandom);
        }
        aAnswer->init(stage);
        mRecorder.afterInitStage(stage);

        while (!stage.isEnd() && stage.turn() < Parameter::GameTurnLimit) {
            // ターン開始
            for (auto& random : laneRandom) {
                random.spin(randomSpinZ);
            }

            // まずは開始フェーズ
            stage.processStartPhase();

            // その後プレイヤーからの干渉を処理
            Action action;
            action = aAnswer->decideNextAction(stage);
            stage.processPlayerPhase(action);

            // 最後に終了フェーズを処理
            stage.processEndPhase(&laneRandom);

            // これで 1 ターン終了
            stage.advanceTurn();
            mRecorder.afterAdvanceTurn(stage);
        }

        mRecorder.afterFinishStage();
        aAnswer->finalize(stage);
    }
    mRecorder.afterFinishAllStages();

    mTimer.stop();
}

//------------------------------------------------------------------------------
const Recorder& Game::recorder() const
{
    return mRecorder;
}

//------------------------------------------------------------------------------
const Timer& Game::timer() const
{
    return mTimer;
}

} // namespace
// EOF
