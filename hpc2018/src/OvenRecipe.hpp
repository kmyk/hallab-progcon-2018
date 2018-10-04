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

/// オーブンを構築するためのレシピ。
class OvenRecipe
{
public:
    /// @name コンストラクタ
    //@{
    OvenRecipe();
    OvenRecipe(int aWidth, int aHeight);
    //@}

    /// @name 問い合わせ
    //@{
    /// 天板の横幅。
    int width() const;
    /// 天板の縦幅。
    int height() const;
    /// 天板の面積。
    int area() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// 天板の横幅。
    int mWidth;
    /// 天板の縦幅。
    int mHeight;
    //@}
};

} // namespace
// EOF
