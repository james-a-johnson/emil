#include "binaryninjaapi.h"
#include "uitypes.h"
#include "uicontext.h"

extern "C" {
    BN_DECLARE_UI_ABI_VERSION

    BINARYNINJAPLUGIN bool UIPluginInit() {
        return true;
    }
}
