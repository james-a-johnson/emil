#include "emil.h"
#include <iostream>

#include "sidebarwidget.h"
#include "sidebar.h"
#include "uitypes.h"
#include "uicontext.h"

EmilSidebarWidget::EmilSidebarWidget(BinaryViewRef data) : SidebarWidget("Emil"), m_data(data) {}

EmilSidebarWidget::~EmilSidebarWidget() {
    std::cout << "destructor\n";
}

EmilSidebarWidgetType::EmilSidebarWidgetType() : SidebarWidgetType(QImage(":/icons/images/emil.png"), "Emil") {}

extern "C" {
    BN_DECLARE_UI_ABI_VERSION

    BINARYNINJAPLUGIN bool UIPluginInit() {
        Sidebar::addSidebarWidgetType(new EmilSidebarWidgetType());
        return true;
    }
}
