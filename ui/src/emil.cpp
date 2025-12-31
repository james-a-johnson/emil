#include "emil.h"
#include <iostream>
#include <qwidget.h>

#include "sidebarwidget.h"
#include "sidebar.h"
#include "uitypes.h"
#include "uicontext.h"

EmilSidebarWidget::EmilSidebarWidget(BinaryViewRef data) : SidebarWidget("Emil") {
    this->m_data = data;
    this->m_headerWidget = new QWidget();
    this->m_currentFrame = nullptr;
}

EmilSidebarWidget::~EmilSidebarWidget() {
    std::cout << "destructor\n";
    delete this->m_headerWidget;
}

void EmilSidebarWidget::notifyRefresh() {
    std::cout << "refresh\n";
}

EmilSidebarWidgetType::EmilSidebarWidgetType() : SidebarWidgetType(QImage(":/icons/images/emil.png"), "Emil") {}

extern "C" {
    BN_DECLARE_UI_ABI_VERSION

    BINARYNINJAPLUGIN bool UIPluginInit() {
        Sidebar::addSidebarWidgetType(new EmilSidebarWidgetType());
        return true;
    }
}
